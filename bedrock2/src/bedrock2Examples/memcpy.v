
Require Import bedrock2.Array bedrock2.Scalars bedrock2.SepLogAddrArith.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import bedrock2.Syntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation coqutil.Z.Lia.
Require Import Coq.Strings.Ascii.
Require Import bedrock2.ZnWords.


Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

Local Coercion name_of_func (f : func) := fst f.

Definition memcpy : func :=
  let dst := "dst" in
  let src := "src" in
  let num := "num" in
  let i := "i" in
  ("memcpy", ([dst; src; num], nil: list string, bedrock_func_body:(
    i = (coq:(4) * num); while (i) {
      store4(dst + coq:(4) * num - i, load4(src + coq:(4) * num - i));
      i = (i - coq:(4))
    }))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface coqutil.Word.LittleEndian coqutil.Word.Interface.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Z.Lia coqutil.Word.Properties bedrock2.TailRecursion.
Require Import coqutil.Tactics.Tactics.
Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  (*Definition entry : Type := string * Semantics.word * (Semantics.word -> mem -> Prop).*)
  Infix "*" := (sep).  
  Infix "*" := (sep) : type_scope.

  Local Infix "^+" := word.add  (at level 50, left associativity).
  Local Infix "^-" := word.sub  (at level 50, left associativity).
  Local Infix "^*" := word.mul  (at level 50, left associativity).
  Local Notation "/_" := word.of_Z.      (* smaller angle: squeeze a Z into a word *)
  Local Notation "\_" := word.unsigned.  (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
  Notation array32 := (array scalar32 (word.of_Z 4)).
  Notation "l .[[ n |==> xs ]]" := (List.upds l n xs) (left associativity, at level 50).

  Ltac subst_words :=
    repeat match goal with x := _ : word.rep |- _ => subst x end.

     
  Ltac upds_simpl_step :=
     match goal with
     | |- context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] =>
       rewrite <- List.upds_app' by (try reflexivity; ZnWords)
     | H : context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] |- _ =>
       rewrite <- List.upds_app' in H by (try reflexivity; ZnWords)
     end.
   Ltac upds_simpl := unfold List.upd in *; repeat upds_simpl_step.

   Ltac simpl_list_length_exprs ::= rewrite ?List.length_skipn, ?List.firstn_length, ?List.app_length, ?List.length_cons, ?List.length_nil, ?List.repeat_length, ?List.upds_length in *.

   Ltac word_Z_unsigned :=
     match goal with
     | H: context [\_ (/_ ?z)] |- _ => rewrite (word.unsigned_of_Z z) in H; change (word.wrap z) with z in H
     | H: context [/_ (\_ ?z)] |- _ => rewrite (word.of_Z_unsigned z) in H
     | |- context [\_ (/_ ?z)] => rewrite (word.unsigned_of_Z z); change (word.wrap z) with z
     | |- context [/_ (\_ ?z)] => rewrite (word.of_Z_unsigned z)
     end.

 Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
(*
 Global Instance spec_of_memcpy : spec_of "memcpy" :=
    fun functions => forall src_ptr dst_ptr src dst off1 off2 buf1 buf2 num R m t,
        src = src_ptr ^+ /_ (4 * Z.of_nat off1) ->
        dst = dst_ptr ^+ /_ (4 * Z.of_nat off2) ->
        4 * (Z.of_nat off1 + \_ num) < 2^width ->
        4 * (Z.of_nat off2 + \_ num) < 2^width ->
        Z.of_nat off1 + \_ num <= Z.of_nat (List.length buf1) ->
        Z.of_nat off2 + \_ num <= Z.of_nat (List.length buf2) ->
        (array32 src_ptr buf1 * array32 dst_ptr buf2 * R) m ->
        WeakestPrecondition.call functions "memcpy" t m [dst; src; num]
        (fun t' m' rets => t = t' /\ rets = nil /\ (array32 src_ptr buf1 * array32 dst_ptr (buf2.[[off2 |==> List.firstn (Z.to_nat (\_ num)) (List.skipn off1 buf1)]]) * R) m').
 *)
 
  Global Instance spec_of_memcpy : spec_of "memcpy" :=
    fun functions => forall src_ptr dst_ptr src dst buf1 buf2 num R m t,
        let off1 := \_ (src ^- src_ptr) in
        let off2 := \_ (dst ^- dst_ptr) in
        off1 mod 4 = 0 /\ off2 mod 4 = 0 ->
        let n1 := Z.to_nat (off1 / 4) in
        let n2 := Z.to_nat (off2 / 4) in
        off1 + 4 * (\_ num) < 2^width ->
        off2 + 4 * (\_ num) < 2^width ->
        Z.of_nat n1 + \_ num <= Z.of_nat (List.length buf1) ->
        Z.of_nat n2 + \_ num <= Z.of_nat (List.length buf2) ->
        (array32 src_ptr buf1 * array32 dst_ptr buf2 * R) m ->
        WeakestPrecondition.call functions "memcpy" t m [dst; src; num]
        (fun t' m' rets => t = t' /\ rets = nil /\ (array32 src_ptr buf1 * array32 dst_ptr (buf2.[[n2 |==> List.firstn (Z.to_nat (\_ num)) (List.skipn n1 buf1)]]) * R) m').

 
 (*
  Global Instance spec_of_memcpy : spec_of "memcpy" :=
    fun functions => forall src_ptr dst_ptr off1 off2 buf1 buf2 num R m t,
        4 * (Z.of_nat off1 + \_ num) < 2^width ->
        4 * (Z.of_nat off2 + \_ num) < 2^width ->
        Z.of_nat off1 + \_ num <= Z.of_nat (List.length buf1) ->
        Z.of_nat off2 + \_ num <= Z.of_nat (List.length buf2) ->
        (array32 src_ptr buf1 * array32 dst_ptr buf2 * R) m ->
        WeakestPrecondition.call functions "memcpy" t m [dst_ptr ^+ (/_ (4 * Z.of_nat off2)); src_ptr ^+ (/_ (4 * Z.of_nat off1)); num]
        (fun t' m' rets => t = t' /\ rets = nil /\ (array32 src_ptr buf1 * array32 dst_ptr (buf2.[[off2 |==> List.firstn (Z.to_nat (\_ num)) (List.skipn off1 buf1)]]) * R) m').
  *)
  Lemma memcpy_ok : program_logic_goal_for_function! memcpy.
  Proof.
    repeat straightline.
    refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("src"::"dst"::"num"::"i"::nil)%list%string (fun V R T M SRC DST NUM I => PrimitivePair.pair.mk (exists j, V = 4 * \_ NUM - 4 * (Z.of_nat j) /\ V = word.unsigned I /\ SRC = src_ptr ^+ (/_ off1) /\ DST = dst_ptr ^+ (/_ off2) /\ NUM = num /\ (array32 src_ptr buf1 * array32 dst_ptr (List.upds buf2 n2 (List.firstn j (List.skipn n1 buf1))) * R) M) (fun t m src dst num i => t = T /\ i = /_ 0 /\ src = SRC /\ dst = DST /\ num = NUM /\ (array32 src_ptr buf1 * array32 dst_ptr (buf2.[[n2|==>List.firstn (Z.to_nat (\_ num)) (List.skipn n1 buf1)]]) * R) m))) _ _ _ _ _ _ _); cbn [reconstruct map.putmany_of_list HList.tuple.to_list
             HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             
             (* List.repeat *) Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline. }
    { eapply (Z.lt_wf 0). }
    { exists 0%nat.
      split; [auto| split]; [ZnWords| split; [|split; [|split] ] ].
      1, 2, 3: ZnWords.
      cbn[List.firstn].
      rewrite List.upds_nil'.
      ecancel_assumption. }
    { repeat straightline.
      { eexists.
        split.
        { repeat straightline.
          eexists; split; [|reflexivity].
          eapply (array_load_four_of_sep_32bit' src_ptr);
            [ reflexivity | ecancel_assumption| ZnWords| ZnWords| ].
          word_Z_unsigned.
          ZnWords. }
        eapply (array_store_four_of_sep_32bit' dst_ptr);
          [reflexivity| ecancel_assumption | ZnWords|].
        replace ( \_ (/_ 4)) with 4 by ZnWords.
        subst_words.
        split; [ZnWords|split; [ZnWords|] ].
        repeat straightline.
        eexists; eexists; split.
        { exists (S x4).
          split; [auto| split; [ZnWords| split; [|split]; [| |split]; auto] ].
          replace (Z.to_nat (\_(src_ptr ^+ /_ off1 ^+ (/_ 4 ^* num) ^- x3 ^- src_ptr) / 4)) with (n1 + x4)%nat in H8 by ZnWords.
          replace (Z.to_nat (\_ (dst_ptr ^+ /_ off2 ^+ (/_ 4 ^* num) ^- x3 ^- dst_ptr) / 4)) with (n2 + x4)%nat in H8 by ZnWords.
          unfold List.upd in H8.
          rewrite <-List.upds_app' in H8 by (rewrite firstn_length; ZnWords).
          replace (nth (n1 + x4) buf1 (/_ 0)) with (nth x4 (List.skipn n1 buf1) (/_ 0)) in H8.
          2:{ rewrite <-(List.firstn_skipn n1 buf1) at 2.
              rewrite List.app_nth2, List.firstn_length, min_l.
              { f_equal; blia. }
              { ZnWords. }
              { rewrite List.firstn_length, min_l by ZnWords.
                blia. } }
          rewrite List.firstn_nth in H8 by ZnWords.
          ecancel_assumption. }
        split; [ZnWords|auto]. }
       split; [auto| split; [ZnWords| split; [|split]; [| |split]; auto] ].
      replace (Z.to_nat (\_ num)) with x4 by ZnWords.
      ecancel_assumption. }
    repeat straightline.
    split; [auto| split; [auto|ecancel_assumption] ].
  Qed.

  (*
  
  Global Instance spec_of_memcpy : spec_of "memcpy" :=
    fun functions => forall src dst buf buf' num R m t,
        4 * \_ num < 2^width ->
         \_ num <= Z.of_nat (List.length buf) ->
         \_ num <= Z.of_nat (List.length buf') ->
        (array32 src buf * array32 dst buf' * R) m ->
        WeakestPrecondition.call functions "memcpy" t m [dst; src; num]
        (fun t' m' rets => t = t' /\ rets = nil /\ (array32 src buf * array32 dst (buf'.[[0|==>List.firstn (Z.to_nat (\_ num)) buf]]) * R) m').

  

  Lemma memcpy_ok : program_logic_goal_for_function! memcpy.
  Proof.
    repeat straightline.
    refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("src"::"dst"::"num"::"i"::nil)%list%string (fun V R T M SRC DST NUM I => PrimitivePair.pair.mk (exists j, V = 4 * \_ NUM - 4 * (Z.of_nat j) /\ V = word.unsigned I /\ SRC = src /\ DST = dst /\ NUM = num /\ (array32 src buf * array32 dst (List.upds buf' 0%nat (List.firstn j buf)) * R) M) (fun t m src dst num i => t = T /\ i = /_ 0 /\ src = SRC /\ dst = DST /\ num = NUM /\ (array32 src buf * array32 dst (buf'.[[0|==>List.firstn (Z.to_nat (\_ num)) buf]]) * R) m))) _ _ _ _ _ _ _); cbn [reconstruct map.putmany_of_list HList.tuple.to_list
             HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             
             (* List.repeat *) Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline. }
    { eapply (Z.lt_wf 0). }
    { exists 0%nat.
      split; [auto| split; [ZnWords| split; [|split]; [| |split]; auto ] ].
      cbn[List.firstn].
      rewrite List.upds_nil'.
      ecancel_assumption. }
    { repeat straightline.
      { eexists.
        split.
        { repeat straightline.
          eexists; split; [|reflexivity].
          erewrite (array_load_four_of_sep_32bit' src);
            [reflexivity | reflexivity | ecancel_assumption| ZnWords | ZnWords| ].
          replace ( \_ (/_ 4)) with 4 by ZnWords.
          ZnWords. }
        eapply (array_store_four_of_sep_32bit' dst);
          [reflexivity| ecancel_assumption | ZnWords|].
        replace ( \_ (/_ 4)) with 4 by ZnWords.
        subst_words.
        split; [ZnWords|split; [ZnWords|] ].
        repeat straightline.
        eexists; eexists; split.
        { exists (S x4).
          split; [auto| split; [ZnWords| split; [|split]; [| |split]; auto] ].
          upds_simpl.
          replace (Z.to_nat (\_(src ^+ (/_ 4 ^* num) ^- x3 ^- src) / 4)) with x4 in H5 by ZnWords.
          rewrite List.firstn_nth in H5 by ZnWords.
          ecancel_assumption. }
        split; [ZnWords|auto]. }
      split; [auto| split; [ZnWords| split; [|split]; [| |split]; auto] ].
      replace (Z.to_nat (\_ num)) with x4 by ZnWords.
      ecancel_assumption. }
    repeat straightline.
    split; [auto| split; [auto|ecancel_assumption] ].
  Qed.
*)
End WithParameters.
