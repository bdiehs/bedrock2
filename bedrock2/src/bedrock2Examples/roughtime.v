
Require Import bedrock2.BasicCSyntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Require Import bedrock2.Array bedrock2.Scalars.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation.
From bedrock2.Map Require Import Separation SeparationLogic.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type := String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition createTimestampMessage :=
  let buffer := "buffer" in
  ("createTimestampMessage", ([buffer], []:list String.string, bedrock_func_body:(
    store4(buffer, constr:(Ox"5"));
    store4(buffer + constr:(4), constr:(Ox"40"));
    store4(buffer + constr:(8), constr:(Ox"40"));
    store4(buffer + constr:(12), constr:(Ox"a4"));
    store4(buffer + constr:(16), constr:(Ox"13c"))
  (*TODO*)
))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface coqutil.Word.LittleEndian coqutil.Word.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Z.Lia coqutil.Word.Properties.


Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  (*TODO: fix this*)
  Definition val : list (string * (list byte)) :=
    [("SREP", List.repeat (Init.Byte.x42) 64);
    ("SIG", List.repeat (Init.Byte.x42) 64);
    ("INDX", List.repeat (Init.Byte.x42) 64);
    ("PATH", List.repeat (Init.Byte.x42) 64);
    ("CERT", List.repeat (Init.Byte.x42) 64)].

  (*Definition tag_to_word32 : String.string -> parameters.word.
  Admitted.*)
  
  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope. Local Infix "*" := sep.
  Check (array scalar32 (word.of_Z 4)).
  Notation array32 := (array scalar32 (word.of_Z 4)).
  Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" := fun functions =>
    forall p_addr buf R m t,
      (sep ((array32) p_addr buf) R) m ->
      List.length buf = 5%nat ->
      WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr]
      (fun t' m' rets => t = t' /\ rets = nil /\
         exists offsets, (scalar32 p_addr (word.of_Z (Z.of_nat (List.length val))) * array32 (word.add p_addr (word.of_Z 4)) (List.map (fun t => word.of_Z t) offsets) * R) m').

   Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).  

   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
    (*Set Printing Implicit.
    Set Printing Coercions.*)
    repeat straightline.
    do 5 (destruct buf; [inversion H0|]).
    destruct buf; [| inversion H0].
    cbn[Array.array] in H.

    repeat straightline.
    replace (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 8)) in *. 2: ring.
    replace (word.add (word.add p_addr (word.of_Z 8)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 12)) in *. 2: ring.
    replace (word.add (word.add p_addr (word.of_Z 12)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 16)) in *. 2: ring.
    repeat straightline.
    split; [auto|].
    split; [auto|].

    exists [64; 64; 164; 316].
    cbn[List.map Array.array].

    replace (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 8)) in *. 2: ring.
    replace (word.add (word.add p_addr (word.of_Z 8)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 12)) in *. 2: ring.
    replace (word.add (word.add p_addr (word.of_Z 12)) (word.of_Z 4)) with
      (word.add p_addr (word.of_Z 16)) in *. 2: ring.
    unfold v, v0, v1, v2, v3 in *.
    repeat (rewrite word.unsigned_of_Z in H5).
    unfold word.wrap in H5.
    repeat (rewrite Zmod_small in H5; [|admit]).
    
    cbn[val Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ].
    unfold a, a0, a1, a2 in H5.
    (*cancel_seps_at_indices 0%nat 3%nat.*)
    ecancel_assumption.
Abort.
(*TODO:
      - write sep logic for general dictionary with list (string, byte)
      - blia
      - write more bedrock code (write the actual response)
*)

End WithParameters.

