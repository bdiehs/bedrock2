
Require Import bedrock2.Array bedrock2.Scalars bedrock2.SepLogAddrArith.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import bedrock2.Syntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation coqutil.Z.Lia.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type :=
  String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition stringToHex (s : string) : Z := Ox"ffffffff".

Lemma stringHexBound : forall s, 0 <= stringToHex s < 2^32.
Proof. intros s. unfold stringToHex. cbn. blia. Qed.

Definition createTimestampMessage :=
  let buffer := "buffer" in
  let i := "i" in
  ("createTimestampMessage", ([buffer], []:list String.string, bedrock_func_body:(
    store4(buffer, coq:(Ox"5"));
    store4(buffer + coq:(4), coq:(Ox"40"));
    store4(buffer + coq:(8), coq:(Ox"40"));
    store4(buffer + coq:(12), coq:(Ox"a4"));
    store4(buffer + coq:(16), coq:(Ox"13c"));

    store4(buffer + coq:(20), coq:(stringToHex "SIG"));
    store4(buffer + coq:(24), coq:(stringToHex "PATH"));
    store4(buffer + coq:(28), coq:(stringToHex "SREP"));
    store4(buffer + coq:(32), coq:(stringToHex "CERT"));
    store4(buffer + coq:(36), coq:(stringToHex "INDX"));

    i = (coq:(64)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(100) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(104), coq:(Ox"3"));
    store4(buffer + coq:(108), coq:(Ox"4"));
    store4(buffer + coq:(112), coq:(Ox"c"));

    store4(buffer + coq:(116), coq:(stringToHex "RADI"));
    store4(buffer + coq:(120), coq:(stringToHex "MIDP"));
    store4(buffer + coq:(124), coq:(stringToHex "ROOT"));
    
    store4(buffer + coq:(128), coq:(Ox"42424242"));
    store(buffer + coq:(232), coq:(Ox"4242424242424242"))
  ))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface coqutil.Word.LittleEndian coqutil.Word.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Z.Lia coqutil.Word.Properties bedrock2.TailRecursion.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rewr.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Definition entry: Type := string * Semantics.word * (Semantics.word -> mem -> Prop).

  Infix "*" := (sep).
  Infix "*" := (sep) : type_scope.

  Infix "+" := (word.add).
  Infix "+" := (word.add) : type_scope.

  
  Notation array32 := (array scalar32 (word.of_Z 4)).
  
  Definition stringToWord (s : string) := word.of_Z (stringToHex s).

  Definition size_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    scalar32 addr (word.of_Z (Z.of_nat (List.length entries))).
  
  Definition offsets_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr + (word.of_Z 4)) 
            (List.map (fun entry => (snd (fst entry))) (tl entries)).
  
  Definition tags_offset (entries : list entry) :=
    (4 + 4 * (List.length (tl entries)))%nat.
  
  Definition tags_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr + (word.of_Z (Z.of_nat (tags_offset entries))))
            (List.map (fun entry => stringToWord (fst (fst entry))) entries).

  Definition contents_offset (entries : list entry) :=
    (tags_offset entries + 4 * (List.length entries))%nat.
  
  Definition message_ok (addr: Semantics.word) (entries : list entry): mem -> Prop :=
    size_field addr entries * offsets_field addr entries * tags_field addr entries *
    let current_addr := addr + (word.of_Z (Z.of_nat (contents_offset entries))) in
    List.fold_left (fun P entry => (snd entry) (current_addr + (snd (fst entry))) * P)
                   entries (emp True).
  
  Definition repeat_dummy n := fun addr => array32 (addr: Semantics.word) (List.repeat (word.of_Z (Ox"42")) n).

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
      List.length buf = 1024%nat ->
      WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr]
      (fun t' m' rets => t = t' /\ rets = nil /\ (message_ok p_addr message_val * R) m'). 
  
   Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
  
   Ltac subst_words :=
     repeat match goal with x := _ : word.rep |- _ => subst x end.
   
   Notation "a |-> v" := (scalar32 a (word.of_Z v)) (at level 30).
   Notation lit := (@word.of_Z (@width (@semantics_parameters p))
                               (@Semantics.word (@semantics_parameters p))).

   Ltac word_simplify :=
       match goal with
       | |- context [?a + ?b] => progress (ring_simplify (a + b))
       | |- context [word.sub ?a ?b] => progress (ring_simplify (word.sub a b))
       | |- context [ (word.unsigned (word.of_Z ?z))] => rewrite (word.unsigned_of_Z z); replace (word.wrap z) with z by (cbn; blia)
       | |- context [word.of_Z (word.unsigned ?z)] => rewrite (word.of_Z_unsigned z)
       end.

   Ltac word_simplify_in H :=
       match type of H with 
       | context [?a + ?b] => progress (ring_simplify (a + b) in H)
       | context [word.sub ?a ?b] => progress (ring_simplify (word.sub a b) in H)
       | context [word.unsigned (word.of_Z ?z)] => rewrite (word.unsigned_of_Z z) in H; replace (word.wrap z) with z in H by (cbn; blia)
       | context [word.of_Z (word.unsigned ?z)] => rewrite (word.of_Z_unsigned z) in H
       end.

   Ltac word_unwrap t :=
     unfold word.wrap; rewrite Zmod_small; [| assert (0 <= t < 2^32) by blia; assumption].

   Ltac word_unwrap_in t H :=
     unfold word.wrap in H; rewrite Zmod_small in H; [| assert (0 <= t < 2^32) by blia; assumption].

   Definition todo : False. Admitted.
   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     do 10 (destruct buf; [inversion H0|]).
     inversion H0; clear H0.
     cbn[Array.array] in H.
     do 9 (word_simplify_in H).
     repeat straightline.
     subst_words.
     clear H9 H8 H7 H6 H5 H4 H3 H1 H0 H.
     repeat word_simplify_in H10.
     
     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       exists i, V = 64 - 4 * (Z.of_nat i) /\
       V = word.unsigned I /\ (i < 16)%nat /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; 4294967295; 4294967295; 4294967295; 4294967295; 4294967295]) * R) M
       )) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist

           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

     { repeat straightline. }
     { eapply (Z.lt_wf 0). }
     { repeat straightline.
       shelve. }
     { exists 0%nat.
       split; auto.
       split; word_simplify; try split; try split; try blia; auto.
       word_simplify.
       cbn [List.repeat Array.array List.skipn List.map].
       repeat word_simplify.
       ecancel_assumption. }
     repeat straightline.
     subst_words.
     subst v.
     word_simplify.
     do 3 (word_simplify_in H4).
     assert (List.length (List.skipn x1 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
     destruct (List.skipn x1 buf) eqn:H17; try contradiction.
     array_app_cons_sep.
     repeat straightline.
     { subst_words.
       eexists; auto.
       split.
       - exists (1 + x1)%nat.
         replace (64 - 4 * Z.of_nat (1 + x1)) with (60 - 4 * Z.of_nat x1) by blia.
         split; auto.
         split; try split; try split; auto.
         { rewrite word.unsigned_sub.
           word_simplify.
           word_unwrap (word.unsigned x - 4).
           blia.
         }
         { rewrite word.unsigned_sub in H5.
           word_simplify_in H5.
           word_unwrap_in (word.unsigned x - 4) H5.
           blia.
         }
         pose proof (f_equal word.of_Z H).
         word_simplify_in H6.
         rewrite H6 in H3.
         change (1 + x1)%nat with (S x1)%nat.
         cbn [List.repeat].
         rewrite repeat_cons.
         array_app_cons_sep.
         rewrite repeat_length, <- List.tl_skipn, H17.
         cbn[List.tl].
         Set Ltac Profiling.
         repeat word_simplify.
         Show Ltac Profile.
         repeat word_simplify_in H3.
         change (66) with (Ox "42") in H3.
         ecancel_assumption.
       - blia.
     }
     clear H4.
     subst br.
     rewrite word.unsigned_sub in H5.
     word_simplify_in H5.
     word_unwrap_in (word.unsigned x - 4) H5.
     assert (word.unsigned x = 4) by blia.
     pose proof (f_equal word.of_Z H4).
     word_simplify_in H6.
     rewrite H6 in H3, H.
     repeat word_simplify_in H3.
     word_simplify_in H.
     assert (x1 = 15)%nat by blia.
     clear H4; clear H6; clear H5.
     rewrite H7 in *; clear H7.
     clear H; clear H1.
     pose proof (f_equal (@List.length _) (firstn_skipn 15 buf)).
     rewrite H2, app_length, firstn_length, H17, List.length_cons, H2 in H.
     assert (List.length l0 = 998)%nat by blia.
     exfalso.
     exact todo.
   
                                 
   
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
     word_simplify.
   Admitted.
   
End WithParameters.

