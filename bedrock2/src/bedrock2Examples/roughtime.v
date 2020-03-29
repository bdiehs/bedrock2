
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


Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Context {word32 : Word.Interface.word 32}.
  Local Notation bytes4 := (array (T := word32) scalar32 (word.of_Z 4)).

  (*TODO: fix this*)
  Definition val : list (string * (list byte)) :=
    [("SREP", List.repeat (Init.Byte.x42) 64);
    ("SIG", List.repeat (Init.Byte.x42) 64);
    ("INDX", List.repeat (Init.Byte.x42) 64);
    ("PATH", List.repeat (Init.Byte.x42) 64);
    ("CERT", List.repeat (Init.Byte.x42) 64)].

  Definition tag_to_word32 : String.string -> word32.
  Admitted.

  Definition word32_of_nat : nat -> word32.
  Admitted.

  Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" := fun functions =>
    forall p_addr R m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions "createTimestampMessage" t m [p_addr] (fun t' m' rets => t = t' /\ exists offsets, sep (scalar32 p_addr (word32_of_nat (List.length val))) (sep (bytes4 (word.add p_addr (word.of_Z 4)) (List.map (fun t => word32_of_nat t) offsets)) R) m').

  Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
  Proof.
    repeat straightline.
    eapply store_four_of_sep with (oldvalue := word.of_Z 5). 1: admit.
    repeat straightline.
    eapply store_four_of_sep with (oldvalue := word.of_Z 5). 1: admit.
    repeat straightline.
    eapply store_four_of_sep with (oldvalue := word.of_Z 5). 1: admit.
    repeat straightline.
    split; auto.
    repeat straightline.
    exists [64%nat; 64%nat; 164%nat; 316%nat].

   Abort.

