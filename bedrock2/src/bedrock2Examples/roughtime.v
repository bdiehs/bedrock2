
Require Import bedrock2.Syntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Require Import bedrock2.Array bedrock2.Scalars.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation.
From bedrock2.Map Require Import Separation SeparationLogic.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type :=
  String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition stringToHex (s : string) : Z.
Admitted.

Lemma stringHexBound : forall s, 0 <= stringToHex s < 2^32.
Proof. Admitted.

Definition createTimestampMessage :=
  let buffer := "buffer" in
  ("createTimestampMessage", ([buffer], []:list String.string, bedrock_func_body:(
    store4(buffer, constr:(Ox"5"));
    store4(buffer + constr:(4), constr:(Ox"40"));
    store4(buffer + constr:(8), constr:(Ox"40"));
    store4(buffer + constr:(12), constr:(Ox"a4"));
    store4(buffer + constr:(16), constr:(Ox"13c"));

    store4(buffer + constr:(20), constr:(stringToHex "SIG"));
    store4(buffer + constr:(24), constr:(stringToHex "PATH"));
    store4(buffer + constr:(28), constr:(stringToHex "SREP"));
    store4(buffer + constr:(32), constr:(stringToHex "CERT"));
    store4(buffer + constr:(36), constr:(stringToHex "INDX"))

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

  Definition entry: Type := string * Semantics.word * (Semantics.word -> mem -> Prop).

  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope.
  Local Infix "+" := word.add.
  Notation array32 := (array scalar32 (word.of_Z 4)).
  Definition stringToWord (s : string) := word.of_Z (stringToHex s).


  Definition size_ok (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    scalar32 addr (word.of_Z (Z.of_nat (List.length entries))).
  Definition offsets_ok (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr + (word.of_Z 4)) (match entries with | [] => [] | h::tail =>
            (List.map (fun entry => stringToWord (fst (fst entry))) tail) end).
  Definition tags_offset (sz: nat) := match sz with
                                    | (0%nat) => 4%nat
                                    | _ => (4%nat * sz)%nat
                                    end.
  Definition tags_ok (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr + (word.of_Z (Z.of_nat (tags_offset (List.length entries)))))
            (List.map (fun entry => stringToWord (fst (fst entry))) entries).

  Definition contents_offset (sz: nat) := (tags_offset sz + sz)%nat.
  
  Fixpoint message_ok (addr: Semantics.word) (entries : list entry): mem -> Prop :=
    size_ok addr entries * offsets_ok addr entries * tags_ok addr entries *
    let current_addr := addr + (word.of_Z (Z.of_nat (contents_offset (List.length entries)))) in
    List.fold_left (fun P entry => (snd entry) (current_addr + (snd (fst entry))) * P)
                   entries (emp True).

  
  Definition repeat_dummy n := fun addr => array32 addr (List.repeat (word.of_Z 66) n).

  Definition srep_val : list entry :=
    [("RADI", word.of_Z 0, repeat_dummy 4);
    ("MIDP", word.of_Z 4, repeat_dummy 8);
    ("ROOT", word.of_Z 12, repeat_dummy 64)
    ].
  
  Definition message_val : list entry :=
    [("SIG", word.of_Z 0, repeat_dummy 64);
    ("PATH", word.of_Z 64, repeat_dummy 64);
    ("SREP", word.of_Z 64, fun addr => message_ok addr srep_val);
    ("CERT", word.of_Z 164, repeat_dummy 64);
    ("INDX", word.of_Z 316, repeat_dummy 64)
    ].
    

  Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" := fun functions =>
    forall p_addr buf R m t,
      ((array32 p_addr buf) * R) m ->
      List.length buf = 10%nat ->
      WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr]
      (fun t' m' rets => t = t' /\ rets = nil /\ (message_ok p_addr message_val * R) m'). 
  
   Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

   Lemma word_add_simplify (w: Semantics.word) (x y: Z) :
        w + (word.of_Z x) + (word.of_Z y) = w + (word.of_Z (x + y)).
   Proof.
     ring.
   Qed.

   Ltac word_simplify := repeat (rewrite word_add_simplify in *); cbv[Z.add Pos.add Pos.succ] in *.
   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     (* Start with header *)
     do 10 (destruct buf; [inversion H0|]).
     destruct buf; [| inversion H0].
     cbn[Array.array] in H.
     word_simplify.
     repeat straightline.
     split; [auto|].
     split; [auto|].
     unfold v, v0, v1, v2, v3, v4, v5, v6, v7, v8 in *.
     repeat (rewrite word.unsigned_of_Z in H10).
     unfold word.wrap in H10.
     repeat (rewrite Zmod_small in H10 ;
             [|change width with 32; try apply stringHexBound; blia]).
     unfold a, a0, a1, a2, a3, a4, a5, a6, a7 in H10.
     simpl.
     unfold size_ok, offsets_ok, tags_ok, contents_offset, tags_offset.
     simpl.
   Admitted.
   
End WithParameters.

