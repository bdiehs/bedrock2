Require Import coqutil.Macros.unique.
Require Import coqutil.Decidable.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import coqutil.Z.Lia.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.Utility.
Require Import coqutil.Datatypes.ListSet.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.RegisterNames.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface.
Require Import compiler.SeparationLogic.
Require Import riscv.Spec.Decode.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Definition valid_instructions(iset: InstructionSet)(prog: list Instruction): Prop :=
  forall instr, In instr prog -> verify instr iset.

(* x0 is the constant 0, x1 is ra, x2 is sp, the others are usable *)
Definition valid_FlatImp_var(x: Z): Prop := 3 <= x < 32.

Lemma valid_FlatImp_var_implies_valid_register: forall (x: Z),
    valid_FlatImp_var x -> valid_register x.
Proof. unfold valid_FlatImp_var, valid_register. intros. blia. Qed.

Module Import FlatToRiscvDef.

  Class parameters := {
    (* the words implementations are not needed, but we need width,
       and EmitsValid needs width_cases *)
    W :> Utility.Words;
    funname_env :> forall T: Type, map.map String.string T; (* abstract T for better reusability *)
    compile_ext_call: funname_env Z -> Z -> Z -> stmt Z -> list Instruction;
  }.

End FlatToRiscvDef.

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscvDef.parameters}.

  (* Part 1: Definitions needed to state when compilation outputs valid code *)

  (* If stmt_size is < 2^10, it is compiled to < 2^10 instructions, which is
     < 2^12 bytes, and the branch instructions have 12 bits to encode the
     relative jump length. One of them is used for the sign, and the other
     11 encode the jump length as a multiple of 2, so jump lengths have to
     be < 2^12 bytes, i.e. < 2^10 instructions, so this bound is tight,
     unless we start using multi-instruction jumps. *)
  Definition stmt_not_too_big(s: stmt Z): Prop := stmt_size s < 2 ^ 10.

  Definition valid_registers_bcond: bcond Z -> Prop := ForallVars_bcond valid_register.
  Definition valid_FlatImp_vars_bcond: bcond Z -> Prop := ForallVars_bcond valid_FlatImp_var.

  Lemma valid_FlatImp_vars_bcond_implies_valid_registers_bcond: forall b,
      valid_FlatImp_vars_bcond b -> valid_registers_bcond b.
  Proof.
    unfold valid_FlatImp_vars_bcond, valid_registers_bcond.
    intros. eauto using ForallVars_bcond_impl, valid_FlatImp_var_implies_valid_register.
  Qed.

  Definition valid_FlatImp_vars: stmt Z -> Prop := ForallVars_stmt valid_FlatImp_var.

  Definition valid_FlatImp_fun: list Z * list Z * stmt Z -> Prop :=
    fun '(argnames, retnames, body) =>
      Forall valid_FlatImp_var argnames /\
      Forall valid_FlatImp_var retnames /\
      valid_FlatImp_vars body /\
      NoDup argnames /\
      NoDup retnames /\
      stmt_not_too_big body.


  (* Part 2: compilation *)

  (* load & store depend on the bitwidth: on 32-bit machines, Lw just loads 4 bytes,
     while on 64-bit machines, it loads 4 bytes and sign-extends them.
     If we want a command which always loads 4 bytes without sign-extending them,
     we need to make a case distinction on the bitwidth and choose Lw on 32-bit,
     but Lwu on 64-bit.
     We can't just always choose Lwu, because Lwu is not available on 32-bit machines. *)

  Definition compile_load(sz: access_size):
    Z -> Z -> Z -> Instruction :=
    match sz with
    | access_size.one => Lbu
    | access_size.two => Lhu
    | access_size.four => if width =? 32 then Lw else Lwu
    | access_size.word => if width =? 32 then Lw else Ld
    end.

  Definition compile_store(sz: access_size):
    Z -> Z -> Z -> Instruction :=
    match sz with
    | access_size.one => Sb
    | access_size.two => Sh
    | access_size.four => Sw
    | access_size.word => if width =? 32 then Sw else Sd
    end.

  Definition compile_op(rd: Z)(op: Syntax.bopname)(rs1 rs2: Z): list Instruction :=
    match op with
    | Syntax.bopname.add => [[Add rd rs1 rs2]]
    | Syntax.bopname.sub => [[Sub rd rs1 rs2]]
    | Syntax.bopname.mul => [[Mul rd rs1 rs2]]
    | Syntax.bopname.mulhuu => [[Mulhu rd rs1 rs2]]
    | Syntax.bopname.divu => [[Divu rd rs1 rs2]]
    | Syntax.bopname.remu => [[Remu rd rs1 rs2]]
    | Syntax.bopname.and => [[And rd rs1 rs2]]
    | Syntax.bopname.or  => [[Or  rd rs1 rs2]]
    | Syntax.bopname.xor => [[Xor rd rs1 rs2]]
    | Syntax.bopname.sru => [[Srl rd rs1 rs2]]
    | Syntax.bopname.slu => [[Sll rd rs1 rs2]]
    | Syntax.bopname.srs => [[Sra rd rs1 rs2]]
    | Syntax.bopname.lts => [[Slt rd rs1 rs2]]
    | Syntax.bopname.ltu => [[Sltu rd rs1 rs2]]
    | Syntax.bopname.eq  => [[Sub rd rs1 rs2; Seqz rd rd]]
    end.

  Definition compile_lit_12bit(rd: Z)(v: Z): list Instruction :=
    [[ Addi rd Register0 (signExtend 12 v) ]].

  (* On a 64bit machine, loading a constant -2^31 <= v < 2^31 is not always possible with
     a Lui followed by an Addi:
     If the constant is of the form 0x7ffffXXX, and XXX has its highest bit set, we would
     have to put 0x80000--- into the Lui, but then that value will be sign-extended.

     Or spelled differently:
     If we consider all possible combinations of a Lui followed by an Addi, we get 2^32
     different values, but some of them are not in the range -2^31 <= v < 2^31.
     On the other hand, this property holds for combining Lui followed by a Xori.

     Or yet differently:
     Lui 0x80000--- ; Addi 0xXXX
     where XXX has the highest bit set,
     loads a value < 2^31, so some Lui+Addi pairs do not load a value in the range
     -2^31 <= v < 2^31, so some Lui+Addi pairs are "wasted" and we won't find a
     Lui+Addi pairs for all desired values in the range -2^31 <= v < 2^31
 *)

  Definition compile_lit_32bit(rd: Z)(v: Z): list Instruction :=
    let lo := signExtend 12 v in
    let hi := Z.lxor (signExtend 32 v) lo in
    [[ Lui rd hi ; Xori rd rd lo ]].

  Definition compile_lit_64bit(rd: Z)(v: Z): list Instruction :=
    let v0 := bitSlice v  0 11 in
    let v1 := bitSlice v 11 22 in
    let v2 := bitSlice v 22 32 in
    let hi := bitSlice v 32 64 in
    compile_lit_32bit rd (signExtend 32 hi) ++
    [[ Slli rd rd 10 ;
       Xori rd rd v2 ;
       Slli rd rd 11 ;
       Xori rd rd v1 ;
       Slli rd rd 11 ;
       Xori rd rd v0 ]].

  Definition compile_lit(rd: Z)(v: Z): list Instruction :=
    if ((-2^11 <=? v)%Z && (v <? 2^11)%Z)%bool then
      compile_lit_12bit rd v
    else if ((width =? 32)%Z || (- 2 ^ 31 <=? v)%Z && (v <? 2 ^ 31)%Z)%bool then
      compile_lit_32bit rd v
    else compile_lit_64bit rd v.

  (* Inverts the branch condition. *)
  Definition compile_bcond_by_inverting
             (cond: bcond Z) (amt: Z) : Instruction:=
    match cond with
    | CondBinary op x y =>
        match op with
        | BEq  => Bne x y amt
        | BNe  => Beq x y amt
        | BLt  => Bge x y amt
        | BGe  => Blt x y amt
        | BLtu => Bgeu x y amt
        | BGeu => Bltu x y amt
        end
    | CondNez x =>
        Beq x Register0 amt
    end.

  Fixpoint save_regs(regs: list Z)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_store access_size.word sp r offset
                   :: (save_regs regs (offset + bytes_per_word))
    end.

  Fixpoint load_regs(regs: list Z)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_load access_size.word r sp offset
                   :: (load_regs regs (offset + bytes_per_word))
    end.

  (* number of words of stack allocation space needed within current frame *)
  Fixpoint stackalloc_words(s: stmt Z): Z :=
    match s with
    | SLoad _ _ _ _ | SStore _ _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _
    | SSkip | SCall _ _ _ | SInteract _ _ _ => 0
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => Z.max (stackalloc_words s1) (stackalloc_words s2)
    (* ignore negative values, and round up values that are not divisible by bytes_per_word *)
    | SStackalloc x n body => (Z.max 0 n + bytes_per_word - 1) / bytes_per_word
                              + stackalloc_words body
    end.

  (* All positions are relative to the beginning of the progam, so we get completely
     position independent code. *)

  Context {env: map.map String.string (list Z * list Z * stmt Z)}.

  Section WithEnv.
    Variable e: funname_env Z.

    (* mypos: position of the code relative to the positions in e
       stackoffset: $sp + stackoffset is the (last) highest used stack address (for SStackalloc)
       s: statement to be compiled *)
    Fixpoint compile_stmt(mypos: Z)(stackoffset: Z)(s: stmt Z): list Instruction :=
      match s with
      | SLoad  sz x y ofs => [[compile_load  sz x y ofs]]
      | SStore sz x y ofs => [[compile_store sz x y ofs]]
      | SStackalloc x n body =>
          [[Addi x sp (stackoffset-n)]] ++ compile_stmt (mypos + 4) (stackoffset-n) body
      | SLit x v => compile_lit x v
      | SOp x op y z => compile_op x op y z
      | SSet x y => [[Add x Register0 y]]
      | SIf cond bThen bElse =>
          let bThen' := compile_stmt (mypos + 4) stackoffset bThen in
          let bElse' := compile_stmt (mypos + 4 + 4 * Z.of_nat (length bThen') + 4) stackoffset bElse in
          (* only works if branch lengths are < 2^12 *)
          [[compile_bcond_by_inverting cond ((Z.of_nat (length bThen') + 2) * 4)]] ++
          bThen' ++
          [[Jal Register0 ((Z.of_nat (length bElse') + 1) * 4)]] ++
          bElse'
      | SLoop body1 cond body2 =>
          let body1' := compile_stmt mypos stackoffset body1 in
          let body2' := compile_stmt (mypos + (Z.of_nat (length body1') + 1) * 4) stackoffset body2 in
          (* only works if branch lengths are < 2^12 *)
          body1' ++
          [[compile_bcond_by_inverting cond ((Z.of_nat (length body2') + 2) * 4)]] ++
          body2' ++
          [[Jal Register0 (- Z.of_nat (length body1' + 1 + length body2') * 4)]]
      | SSeq s1 s2 =>
          let s1' := compile_stmt mypos stackoffset s1 in
          let s2' := compile_stmt (mypos + 4 * Z.of_nat (length s1')) stackoffset s2 in
          s1' ++ s2'
      | SSkip => nil
      | SCall resvars f argvars =>
        let fpos := match map.get e f with
                    | Some pos => pos
                    (* don't fail so that we can measure the size of the resulting code *)
                    | None => 42
                    end in
        save_regs argvars (- bytes_per_word * Z.of_nat (length argvars)) ++
        [[ Jal ra (fpos - (mypos + 4 * Z.of_nat (length argvars))) ]] ++
        load_regs resvars (- bytes_per_word * Z.of_nat (length argvars + length resvars))
      | SInteract _ _ _ => compile_ext_call e mypos stackoffset s
      end.

    (*
     Stack layout:

     high addresses              ...
                      old sp --> begin of stack scratch space of previous function
                                 argn
                                 ...
                                 arg0
                                 retn
                                 ...
                                 ret0
                                 ra
                                 mod_var_n
                                 ...
                                 mod_var_0
                                 end of stack scratch space of current function
                                 ...  (stack scratch space also grows downwards, from "end" to "begin")
                      new sp --> begin of stack scratch space of current function
     low addresses               ...

     Expected stack layout at beginning of function call: like above, but only filled up to arg0.
     Stack grows towards low addresses.
    *)
    Definition compile_function(mypos: Z):
      (list Z * list Z * stmt Z) -> list Instruction :=
      fun '(argvars, resvars, body) =>
        let mod_vars := list_union Z.eqb (modVars_as_list Z.eqb body) argvars in
        let scratchwords := stackalloc_words body in
        let framesize := bytes_per_word *
                         (Z.of_nat (length argvars + length resvars + 1 + length mod_vars) + scratchwords) in
        [[ Addi sp sp (-framesize) ]] ++
        [[ compile_store access_size.word sp ra
                         (bytes_per_word * (Z.of_nat (length mod_vars) + scratchwords)) ]] ++
        save_regs mod_vars (bytes_per_word * scratchwords) ++
        load_regs argvars (bytes_per_word * (Z.of_nat (length mod_vars + 1 + length resvars) + scratchwords)) ++
        compile_stmt (mypos + 4 * (2 + Z.of_nat (length mod_vars + length argvars)))
                     (bytes_per_word * scratchwords) body ++
        save_regs resvars (bytes_per_word * (Z.of_nat (length mod_vars + 1) + scratchwords)) ++
        load_regs mod_vars (bytes_per_word * scratchwords) ++
        [[ compile_load access_size.word ra sp
                        (bytes_per_word * (Z.of_nat (length mod_vars) + scratchwords)) ]] ++
        [[ Addi sp sp framesize ]] ++
        [[ Jalr zero ra 0 ]].

    Definition add_compiled_function(state: list Instruction * funname_env Z)(fname: String.string)
               (fimpl: list Z * list Z * stmt Z): list Instruction * funname_env Z :=
      let '(old_insts, posmap) := state in
      let pos := 4 * Z.of_nat (length (old_insts)) in
      let new_insts := compile_function pos fimpl in
      (old_insts ++ new_insts, map.put posmap fname pos).

    Definition compile_funs: env -> list Instruction * funname_env Z :=
      map.fold add_compiled_function (nil, map.empty).
  End WithEnv.

  (* compiles all functions just to obtain their code size *)
  Definition build_fun_pos_env(e_impl: env): funname_env Z :=
    (* since we pass map.empty as the fun_pos_env into compile_funs, the instrs
       returned don't jump to the right positions yet (they all jump to 42),
       but the instructions have the right size, so the posmap we return is correct *)
    let '(instrs, posmap) := compile_funs map.empty e_impl in posmap.

End FlatToRiscv1.
