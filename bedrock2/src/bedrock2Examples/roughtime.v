
Require Import bedrock2.BasicCSyntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Require Import bedrock2.Array bedrock2.Scalars.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
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
    store4(buffer, constr:(5));
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
Require Import coqutil.Z.Lia.


Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Local Notation bytes4 := (array scalar32 (word.of_Z 4)).

  (*TODO: fix this*)
  Definition val : list (string * (list byte)) :=
    [("SREP", List.repeat (Init.Byte.x42) 64);
    ("SIG", List.repeat (Init.Byte.x42) 64);
    ("INDX", List.repeat (Init.Byte.x42) 64);
    ("PATH", List.repeat (Init.Byte.x42) 64);
    ("CERT", List.repeat (Init.Byte.x42) 64)].

  Definition tag_to_word32 : String.string -> parameters.word.
  Admitted.

  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope. Local Infix "*" := sep.
Check bytes4.
  Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" := fun functions =>
    forall p_addr buf R m t,
      (sep (bytes4 p_addr buf) R) m ->
      List.length buf = 5%nat (*TODO: there will actually be a num_bytes instead of this 5 later on*) ->
      WeakestPrecondition.call (p:=@semantics_parameters p) functions "createTimestampMessage" t m [p_addr] (fun t' m' rets => t = t' /\ rets = nil /\ exists offsets, (scalar32 p_addr (word.of_Z (Z.of_nat (List.length val))) * bytes4 (word.add p_addr (word.of_Z 4)) (List.map (fun t => word.of_Z t) offsets) * R) m').


  Require Import coqutil.Word.Properties.
  Local Notation array := (array (mem:=mem) ptsto (word.of_Z 1)).

(* This seemed necessary but on a second thought I don't think so
  Lemma byte4array_address_inbounds xs start a
    (Hmod : word.unsigned (word.sub a start) mod 4 = 0)
    (Hlen : word.unsigned (word.sub a start) < 4 * Z.of_nat (List.length xs))
    (i := Z.to_nat ((word.unsigned (word.sub a start) / 4)))
    : Lift1Prop.iff1 (bytes4 start xs)
      (bytes4 start (firstn i xs) * (
        scalar32 a (hd (word.of_Z 0) (skipn i xs)) *
        bytes4 (word.add a (word.of_Z 4)) (skipn (S i) xs) ) ).
  Proof.
    eapply array_address_inbounds; rewrite word.unsigned_of_Z; auto.
  Qed.

  Lemma byte4array_index_inbounds xs start iw
    (Hmod : word.unsigned iw mod 4 = 0)
    (Hlen : word.unsigned iw < 4 * Z.of_nat (List.length xs))
    (i := Z.to_nat ((word.unsigned iw / 4)))
    : Lift1Prop.iff1 (bytes4 start xs)
      (bytes4 start (firstn i xs) * (
        scalar32 (word.add start iw) (hd (word32_of_nat 0) (skipn i xs)) *
        bytes4 (word.add (word.add start iw) (word.of_Z 4)) (skipn (S i) xs) ) ).
  Proof.
    rewrite (byte4array_address_inbounds xs start (word.add start iw));
    replace (word.sub (word.add start iw) start) with iw; try (reflexivity || assumption).
    all : rewrite word.word_sub_add_l_same_l; trivial.
  Qed.
*)
  Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
  Proof.
    repeat straightline.    
    do 5 (destruct buf; [inversion H0|]).
    destruct buf; [| inversion H0].
    eapply store_four_of_sep.
    1: eapply Lift1Prop.subrelation_iff1_impl1. 2: apply H.
    1: etransitivity. 1: apply sep_assoc. 1: ecancel.
    repeat straightline.
    eapply store_four_of_sep.
    1: eapply Lift1Prop.subrelation_iff1_impl1. 2: apply H2.
    1: etransitivity. 2: ecancel. 1: replace (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4)) with a0. 2: admit(*ring*). 1: ecancel.
    repeat straightline.
    eapply store_four_of_sep.
    1: eapply Lift1Prop.subrelation_iff1_impl1. 2: apply H3.
    1: etransitivity. 2: ecancel. 1: replace (word.add a0 (word.of_Z 4)) with a1. 2: admit(*ring*). 1: ecancel.
    repeat straightline.
    eapply store_four_of_sep.
    1: eapply Lift1Prop.subrelation_iff1_impl1. 2: apply H4.
    1: etransitivity. 2: ecancel. 1: replace (word.add a1 (word.of_Z 4)) with a2. 2: admit(*ring*). 1: ecancel.
    repeat straightline.
    split; [auto|].
    split; [auto|].

    exists [64; 64; 164; 316].
    eapply Lift1Prop.subrelation_iff1_impl1. 2: apply H5.
    simpl. unfold v, v0, v1, v2, v3.
    repeat (rewrite word.unsigned_of_Z).
    unfold word.wrap.

    repeat (rewrite Zmod_small; [|admit(*lia or omega*)]).

    replace a with (word.add p_addr (word.of_Z 4)). 2: admit(*ring*).
    replace a0 with (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4)). 2: admit(*ring*).
    replace a1 with (word.add (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4))
                      (word.of_Z 4)). 2: admit(*ring*).
    replace a2 with (word.add
              (word.add (word.add (word.add p_addr (word.of_Z 4)) (word.of_Z 4))
                        (word.of_Z 4)) (word.of_Z 4)). 2: admit(*ring*).
    try ecancel.
   Abort.

