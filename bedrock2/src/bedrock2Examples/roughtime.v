Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.


Require Import bedrock2.Array bedrock2.Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.

(*Changed array_append' to array_append*)
Ltac get_array_rewr_eq t :=
  lazymatch t with
  | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
    constr:(iff1ToEq (array_append PT SZ xs ys start))
  | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
    constr:(iff1ToEq (array_cons PT SZ x xs start))
  | context [ array ?PT ?SZ ?start nil ] =>
    constr:(iff1ToEq (array_nil PT SZ start))
  end.


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
    store4(buffer, constr:(Ox"5"));
    store4(buffer + constr:(4), constr:(Ox"40"));
    store4(buffer + constr:(8), constr:(Ox"40"));
    store4(buffer + constr:(12), constr:(Ox"a4"));
    store4(buffer + constr:(16), constr:(Ox"13c"));

    store4(buffer + constr:(20), constr:(stringToHex "SIG"));
    store4(buffer + constr:(24), constr:(stringToHex "PATH"));
    store4(buffer + constr:(28), constr:(stringToHex "SREP"));
    store4(buffer + constr:(32), constr:(stringToHex "CERT"));
    store4(buffer + constr:(36), constr:(stringToHex "INDX"));

    i = (constr:(64)); while (i) { i = (i - constr:(4));
      store4(buffer + constr:(100) - i, constr:(Ox"42"))
    };

    store4(buffer + constr:(104), constr:(Ox"3"));
    store4(buffer + constr:(108), constr:(Ox"4"));
    store4(buffer + constr:(112), constr:(Ox"c"));

    store4(buffer + constr:(116), constr:(stringToHex "RADI"));
    store4(buffer + constr:(120), constr:(stringToHex "MIDP"));
    store4(buffer + constr:(124), constr:(stringToHex "ROOT"));
    
    store4(buffer + constr:(128), constr:(Ox"42424242"));
    store(buffer + constr:(232), constr:(Ox"4242424242424242"))
  ))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface coqutil.Word.LittleEndian coqutil.Word.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Z.Lia coqutil.Word.Properties bedrock2.TailRecursion.

(* This can be overridden by the user.
   The idea of a "tag" is that it's a subterm of a sepclause which is so unique that if
   the same tag appears both on the left and on the right of an iff1, we're sure that
   these two clauses should be matched & canceled with each other.
   "tag" should return any Gallina term. *)
Ltac tag P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | _ => fail "no recognizable tag"
  end.

(* This can be overridden by the user.
   The idea of "addr" is that if the addresses of two sepclauses are the same,
   we're sure that these two clauses should be matched & canceled with each other,
   even if they still contain many evars outside of their address.
   "addr" should return a Gallina term of type "word" *)
Ltac addr P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | ptsto ?A _ => A
  | ptsto_word ?A _ => A
  | array _ _ ?A _ => A
  | _ => fail "no recognizable address"
  end.


Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.

Ltac array_app_cons_sep := rewr get_array_rewr_eq in *.

Ltac wseplog_pre :=
  repeat (autounfold with unf_to_array);
  repeat ( rewr get_array_rewr_eq in |-* ).

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Definition entry: Type := string * Semantics.word * (Semantics.word -> mem -> Prop).

  Infix "*" := (sep).
  Infix "*" := (sep) : type_scope.

  Local Infix "+" := word.add.
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
  
  Definition repeat_dummy n := fun addr => array32 (addr: Semantics.word) (List.repeat (word.of_Z 66) n).

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
(*
   Lemma word_add_simplify (w: Semantics.word) (x y: Z) :
        w + (word.of_Z x) + (word.of_Z y) = w + (word.of_Z (x + y)).
   Proof.
     ring.
   Qed.
*)
   Require Import coqutil.Tactics.Tactics.
   (*
   Ltac word_simplify :=
     repeat (rewrite word_add_simplify in * ); cbv[Z.add Pos.add Pos.succ] in *.
*)
   Ltac foo := idtac.
   
   Ltac canonicalize_word_width_and_instance :=  repeat so fun hypergoal => 
     match hypergoal with
     | context [@word.unsigned ?wi ?inst] =>
       let wi' := eval cbn in wi in let inst' := eval cbn in inst in
          progress (change wi with wi' in *; change inst with inst' in * ) 
     | context [@word.signed   ?wi ?inst] => let wi' := eval cbn in wi in let inst' := eval cbn in inst in
          progress ( change wi with wi' in *; change inst with inst' in * ) 
     end.

  
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
       | H: context [?a + ?b] |- _ => progress (ring_simplify (a + b) in H)
       | H: context [word.sub ?a ?b] |- _ => progress (ring_simplify (word.sub a b) in H)
       | H: context [word.unsigned (word.of_Z ?z)] |- _ => rewrite (word.unsigned_of_Z z) in H; replace (word.wrap z) with z in H by (cbn; blia)
       | H: context [word.of_Z (word.unsigned ?z)] |- _ => rewrite (word.of_Z_unsigned z) in H
       end.


   Ltac word_unsigned z := rewrite (word.unsigned_of_Z z); replace (word.wrap z) with z by (cbn; blia).
     
   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     do 10 (destruct buf; [inversion H0|]).
     inversion H0; clear H0.
     cbn[Array.array] in H.

     repeat word_simplify.
     repeat straightline.
     subst_words.
     clear H9 H8 H7 H6 H5 H4 H3 H1 H0 H.
     repeat word_simplify.
     
     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       exists i, V = 64 - 4 * (Z.of_nat i) /\
       V = word.unsigned I /\ V <> 0 /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) *
         (p_addr + lit 36) |-> 4294967295 *
         (word.add p_addr (lit 32) |-> 4294967295 *
          (word.add p_addr (lit 28) |-> 4294967295 *
           (word.add p_addr (lit 24) |-> 4294967295 *
            (word.add p_addr (lit 20) |-> 4294967295 *
             (word.add p_addr (lit 16) |-> 316 *
              (word.add p_addr (lit 12) |-> 164 *
               (word.add p_addr (lit 8) |-> 64 *
                (word.add p_addr (lit 4) |-> 64 *
                 (p_addr |-> 5 * R)))))))))%type) M
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
       repeat (split; trivial; []).
       repeat word_simplify.
       split; try split; try split; try blia; auto.
       cbn [List.repeat Array.array List.skipn].
       ecancel_assumption. }
                             idtac.
     do 10 straightline.
     do 10 straightline.
     do 2 straightline.
     straightline_cleanup.
     subst_words.
     repeat word_simplify.
     
     assert (x = lit v).
     { subst v; rewrite word.of_Z_unsigned; auto. }
     rewrite H.
     assert (List.length (List.skipn (Z.to_nat ((64 - v) / 4)) buf) <> 0%nat).
     { rewrite List.skipn_length, H2. admit. }
     destruct (List.skipn (Z.to_nat ((64 - v) / 4)) buf) eqn:H17; try contradiction.
     array_app_cons_sep.
     word_simplify.
     repeat straightline.
     { subst_words.
       subst v.
       rewrite word.of_Z_unsigned in *.
       eexists; auto.
       split.
       - split; auto.
         split; try split; try split; auto; try blia.
         { rewrite word.unsigned_sub.
           word_simplify.
           admit. }
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { repeat word_simplify.
           f_equal.
           admit. }
         repeat word_simplify.
         replace (Z.to_nat ((64 - word.unsigned (word.sub x0 (lit 4))) / 4)) with ((Z.to_nat ((64 - word.unsigned x0) / 4)) + 1)%nat by admit.

     

     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       let i := Z.to_nat ((64 - V) / 4) in
       V = word.unsigned I /\ V <> 0 /\ V <= 64 /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) *
         (p_addr + lit 36) |-> 4294967295 *
         (word.add p_addr (lit 32) |-> 4294967295 *
          (word.add p_addr (lit 28) |-> 4294967295 *
           (word.add p_addr (lit 24) |-> 4294967295 *
            (word.add p_addr (lit 20) |-> 4294967295 *
             (word.add p_addr (lit 16) |-> 316 *
              (word.add p_addr (lit 12) |-> 164 *
               (word.add p_addr (lit 8) |-> 64 *
                (word.add p_addr (lit 4) |-> 64 *
                 (p_addr |-> 5 * R)))))))))%type) M
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
     { repeat (split; trivial; []).
       repeat word_simplify.
       split; try split; try split; try blia; auto.
       simpl (Z.to_nat _).
       cbn [List.repeat Array.array List.skipn].
       ecancel_assumption. }
     
     
     repeat straightline.
     subst_words.
     repeat word_simplify.
     assert (x = lit v).
     { subst v; rewrite word.of_Z_unsigned; auto. }
     rewrite H.
     assert (List.length (List.skipn (Z.to_nat ((64 - v) / 4)) buf) <> 0%nat).
     { rewrite List.skipn_length, H2. admit. }
     destruct (List.skipn (Z.to_nat ((64 - v) / 4)) buf) eqn:H17; try contradiction.
     array_app_cons_sep.
     word_simplify.
     repeat straightline.
     { subst_words.
       subst v.
       rewrite word.of_Z_unsigned in *.
       eexists; auto.
       split.
       - split; auto.
         split; try split; try split; auto; try blia.
         { rewrite word.unsigned_sub.
           word_simplify.
           admit. }
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { repeat word_simplify.
           f_equal.
           admit. }
         repeat word_simplify.
         replace (Z.to_nat ((64 - word.unsigned (word.sub x0 (lit 4))) / 4)) with ((Z.to_nat ((64 - word.unsigned x0) / 4)) + 1)%nat by admit.
         match goal with
         | |- context [List.repeat ?x (?n + 1)] =>
           replace (List.repeat x (n + 1)) with (List.repeat x n ++ [x]); idtac n
         end.
         { array_app_cons_sep.
           rewrite List.repeat_length.
           rewrite word.unsigned_of_Z.
           change (word.wrap 4) with 4.
           rewrite ZifyInst.of_nat_to_nat_eq.
           assert (0 <> ((64 - word.unsigned x0) / 4)).
           Search 
           { blia.
           unfold Z.max.
           Search Z.of_nat Z.to_nat.
           Search word.of_Z.
           word_simplify.
           rewrite word.of_Z_unsigned.
           repeat word_simplify.
           
           
           match goal with
           | |- context [ @array ?w ?word ?v ?m ?T ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             pose proof iff1ToEq (@array_append w word _ v m _ T PT SZ xs ys start); idtac T
           end.
           rewrite H.
           Set Printing All.
           pose proof iff1ToEq (array_append scalar32 (word.of_Z 4) (List.repeat (lit (Ox "42")) x1) [lit (Ox "42")] (word.add p_addr (lit 40))).
           Unset Printing All.
           rewrite H21.
           Set Printing All.
           
           word_simplify.
         exists (x1 + 1)%nat.
         split. 1: admit.
         split. 1: admit.
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { destruct buf; try inversion H2.
           replace (x1 + 1)%nat with (S x1) by blia.
           rewrite List.skipn_cons.
           admit. }
       
       simpl.
       exists 0%nat; split; try blia.
       split; try f_equal.
       cbn [List.repeat Array.array List.skipn].
       repeat word_simplify.
       ecancel_assumption. }
     repeat straightline.
     subst_words.
     replace (word.sub (p_addr + lit 104) (word.sub (lit (Z.of_nat (64 - 4 * x1))) (lit 4))) with (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * x1)))) by admit.
     
     

     
     

     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       V = word.unsigned I /\ word.unsigned I <> 0 /\ BUFFER = p_addr /\ exists i, (i < 16)%nat /\ I = word.of_Z (Z.of_nat (64 - 4*i)%nat) /\ (array32 (word.add BUFFER (word.of_Z 40)) (List.repeat (lit (Ox"42")) i) * array32 (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4*i)%nat))) (List.skipn i buf) *
         (p_addr + lit 36) |-> lit 4294967295 *
         (word.add p_addr (lit 32) |-> lit 4294967295 *
          (word.add p_addr (lit 28) |-> lit 4294967295 *
           (word.add p_addr (lit 24) |-> lit 4294967295 *
            (word.add p_addr (lit 20) |-> lit 4294967295 *
             (word.add p_addr (lit 16) |-> lit 316 *
              (word.add p_addr (lit 12) |-> lit 164 *
               (word.add p_addr (lit 8) |-> lit 64 *
                (word.add p_addr (lit 4) |-> lit 64 *
                 (p_addr |-> lit 5 * R)))))))))%type) M
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
     { repeat (split; trivial; []).
       split; try split; auto.
       { rewrite word.unsigned_of_Z; cbn; blia. }
       exists 0%nat; split; try blia.
       split; try f_equal.
       cbn [List.repeat Array.array List.skipn].
       repeat word_simplify.
       ecancel_assumption. }
     repeat straightline.
     subst_words.
     replace (word.sub (p_addr + lit 104) (word.sub (lit (Z.of_nat (64 - 4 * x1))) (lit 4))) with (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * x1)))) by admit.
     assert (List.length (List.skipn x1 buf) <> 0%nat).
     { rewrite List.skipn_length; blia. }
     destruct (List.skipn x1 buf) eqn:H17; try contradiction.
     array_app_cons_sep.
     repeat straightline.
     { eexists; auto.
       subst_words.
       split.
       - split; auto.
         split; try split; auto; try blia.
         exists (x1 + 1)%nat.
         split. 1: admit.
         split. 1: admit.
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { destruct buf; try inversion H2.
           replace (x1 + 1)%nat with (S x1) by blia.
           rewrite List.skipn_cons.
           admit. }
         Set Printing All.
         match goal with
         | |- context [List.repeat ?x (?n + 1)] =>
           replace (List.repeat x (n + 1)) with (List.repeat x n ++ [x])
         end.
         Set Printing All.
         {
           match goal with
           | |- context [ @array ?w ?word ?v ?m ?T ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             pose proof iff1ToEq (@array_append w word _ v m _ T PT SZ xs ys start)
           end.
           Set Printing All.
           rewrite H13.
           array_app_cons_sep.
         
     destruct (List.skipn x1 bufl) eqn:H20; try contradiction.
     cbn[Array.array] in H19.
     repeat straightline.
     { eexists; auto.
       subst v9 x.
       split.
       - split; auto.
         split; try split; auto; try blia.
         exists (x1 + 1)%nat.
         split. 1: admit.
         split. 1: admit.
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.

     
     word_simplify.
     (word.sub (p_addr + lit 104) (word.sub (lit (Z.of_nat (64 - 4 * x1))) (lit 4)))
    
     Search Z.of_nat.
     
       simpl (Z.of_nat (4 * 0)).
       cbn [Z.of_nat (4 * 0)].
       
       
       
       subst i; split; try split; auto.
       - rewrite word.unsigned_of_Z.
         unfold word.wrap.
         change width with 32.
         admit.
       - exists 0%nat; split; try blia.
         split; try f_equal.
         cbn [List.repeat Array.array].
         replace (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * 0)))) with (word.add p_addr (word.of_Z 40)) by admit.
         rewrite List.skipn_O.
         ecancel_assumption. }
     repeat straightline.
     subst i a8 x.
     replace (word.sub (p_addr + word.of_Z 104)
       (word.sub (word.of_Z (Z.of_nat (64 - 4 * x1))) (word.of_Z 4))) with (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * x1)))) by admit.

     assert (List.length (List.skipn x1 bufl) <> 0%nat).
     { rewrite List.skipn_length.
       rewrite H11.
       blia. }
     
     
          
     rewrite <- (List.firstn_skipn 16 buf) in H10.
     set (bufr := List.skipn 16 buf) in *.
     set (bufl := List.firstn 16 buf) in *.
     assert (List.length bufl = 16%nat).
     { subst bufl. rewrite List.firstn_length_le; blia. }
     assert (List.length bufr = 998%nat).
     { subst bufr. rewrite List.skipn_length; blia. }

     
     array_app_cons_sep.
     rewrite H11 in H10.
     repeat word_simplify.

     

     (*
     pose proof (array_append scalar32 (word.of_Z 4) bufl bufr) (p_addr + (word.of_Z 40)).
     rewrite H11 in H13.
     replace (word.add (word.add p_addr (word.of_Z 40))
                       (word.of_Z (word.unsigned (word.of_Z 4) * Z.of_nat 16))) with
         (word.add p_addr (word.of_Z 104)) in H13.
     2: { rewrite word.unsigned_of_Z. simpl. rewrite word_add_simplify.
          reflexivity. }
     
     SeparationLogic.seprewrite_in H13 H10.
     *)
     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       V = word.unsigned I /\ word.unsigned I <> 0 /\ BUFFER = p_addr /\ exists i, (i < 16)%nat /\ I = word.of_Z (Z.of_nat (64 - 4*i)%nat) /\ (array32 (word.add BUFFER (word.of_Z 40)) (List.repeat (lit (Ox"42")) i) * (array32 (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4*i)%nat))) (List.skipn i bufl) *
          array32 (word.add p_addr (word.of_Z 104)) bufr)%type *
         (p_addr + lit 36) |-> lit 4294967295 *
         (word.add p_addr (lit 32) |-> lit 4294967295 *
          (word.add p_addr (lit 28) |-> lit 4294967295 *
           (word.add p_addr (lit 24) |-> lit 4294967295 *
            (word.add p_addr (lit 20) |-> lit 4294967295 *
             (word.add p_addr (lit 16) |-> lit 316 *
              (word.add p_addr (lit 12) |-> lit 164 *
               (word.add p_addr (lit 8) |-> lit 64 *
                (word.add p_addr (lit 4) |-> lit 64 *
                 (p_addr |-> lit 5 * R)))))))))%type) M
       )) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist

           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

     (*{  Set Printing All. Check array32.
        Check (fun V T M I BUFFER =>
       V = word.unsigned I /\ word.unsigned I <> 0 /\ BUFFER = p_addr /\ exists i, (i < 16)%nat /\ I = word.of_Z (Z.of_nat (64 - 4*i)%nat) /\ (array32  BUFFER nil) M
       ).*)
     { repeat straightline. }
     { eapply (Z.lt_wf 0). }
     { repeat straightline.
       shelve. }
     { repeat (split; trivial; []).
       subst i; split; try split; auto.
       - rewrite word.unsigned_of_Z.
         unfold word.wrap.
         change width with 32.
         admit.
       - exists 0%nat; split; try blia.
         split; try f_equal.
         cbn [List.repeat Array.array].
         replace (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * 0)))) with (word.add p_addr (word.of_Z 40)) by admit.
         rewrite List.skipn_O.
         ecancel_assumption. }
     repeat straightline.
     subst i a8 x.
     replace (word.sub (p_addr + word.of_Z 104)
       (word.sub (word.of_Z (Z.of_nat (64 - 4 * x1))) (word.of_Z 4))) with (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z (Z.of_nat (4 * x1)))) by admit.

     assert (List.length (List.skipn x1 bufl) <> 0%nat).
     { rewrite List.skipn_length.
       rewrite H11.
       blia. }
     destruct (List.skipn x1 bufl) eqn:H20; try contradiction.
     cbn[Array.array] in H19.
     repeat straightline.
     { eexists; auto.
       subst v9 x.
       split.
       - split; auto.
         split; try split; auto; try blia.
         exists (x1 + 1)%nat.
         split. 1: admit.
         split. 1: admit.
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { admit. }
         match goal with
         | |- context [List.repeat ?x (?n + 1)] =>
           replace (List.repeat x (n + 1)) with (List.repeat x n ++ [x])
         end.
         { 
           match goal with
           | |- context [ @array ?w ?word ?v ?m ?T ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             pose proof iff1ToEq (@array_append w word _ v m _ T PT SZ xs ys start)
           end.
           Set Printing All.
           pose proof iff1ToEq (array_append scalar32 (word.of_Z 4) (List.repeat (lit (Ox "42")) x1) [lit (Ox "42")] (word.add p_addr (lit 40))).
           Unset Printing All.
           rewrite H21.
           Set Printing All.
           
           cbn[seps].
           rewrite H16.
           Set Printing All.
           Check (@Datatypes.app
                (@word.rep (Zpos (xO (xO (xO (xO (xO xH))))))
                   (@Semantics.word (@semantics_parameters p)))
                (@List.repeat
                   (@word.rep (@width (@semantics_parameters p))
                      (@Semantics.word (@semantics_parameters p)))
                   (@word.of_Z (@width (@semantics_parameters p))
                      (@Semantics.word (@semantics_parameters p))
                      (Ox
                         (String
                            (Ascii.Ascii false false true false true true false
                               false)
                            (String
                               (Ascii.Ascii false true false false true true false
                                  false) EmptyString)))) x1)
                (@cons
                   (@word.rep (@width (@semantics_parameters p))
                      (@Semantics.word (@semantics_parameters p)))
                   (@word.of_Z (@width (@semantics_parameters p))
                      (@Semantics.word (@semantics_parameters p))
                      (Ox
                         (String
                            (Ascii.Ascii false false true false true true false
                               false)
                            (String
                               (Ascii.Ascii false true false false true true false
                                  false) EmptyString))))
                   (@nil
                      (@word.rep (@width (@semantics_parameters p))
                         (@Semantics.word (@semantics_parameters p)))))).
           rewrite H16.
           rewr get_array_rewr_eq in *.
           idtac.
           Ltac get_array_rewr_eq t :=
             lazymatch t with
             | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
               constr:(iff1ToEq (array_append PT SZ xs ys start))
             | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
               constr:(iff1ToEq (array_cons PT SZ x xs start))
             | context [ array ?PT ?SZ ?start nil ] =>
               constr:(iff1ToEq (array_nil PT SZ start))
             end.

           rewrite List.repeat_length.
           cbn[seps].
           cancel.
           
           pose proof (array_append scalar32 (word.of_Z 4) (List.repeat (word.of_Z (Ox "42")) x1) [word.of_Z (Ox "42")] (p_addr + word.of_Z 40)).
           SeparationLogic.seprewrite H16.

         
         replace (List.repeat (word.of_Z (Ox "42")) (x1 + 1)) with (List.repeat (word.of_Z (Ox "42")) x1 ++ [word.of_Z (Ox "42")]).
         
         canonicalize_word_width_and_instance.
         
         replace (List.repeat (A := Semantics.word) (word.of_Z (Ox "42")) (x1 + 1)) with (List.repeat (word.of_Z (Ox "42")) x1 ++ [word.of_Z (Ox "42")]).
     
     ring_simplify (word.sub (p_addr + word.of_Z 104)
       (word.sub (word.of_Z (Z.of_nat (64 - 4 * x1))) (word.of_Z 4))).
     straightline.


     
     { repeat (split; trivial; []).
       subst i; split; try split; auto.
       - rewrite word.unsigned_of_Z.
         unfold word.wrap.
         change width with 32.
         admit.
       - exists 0%nat; split. 1: admit.
         cbn [List.repeat Array.array].
         replace (word.add (word.add p_addr (word.of_Z 40)) (word.of_Z 0)) with (word.add p_addr (word.of_Z 40)) by ring.
         rewrite List.skipn_O.
         ecancel_assumption.
     }
     
     repeat straightline.
     assert (List.length (List.skipn x1 bufl) <> 0%nat).
     { rewrite List.skipn_length.
       rewrite <- H17 in H14.
       blia. }
     destruct (List.skipn x1 bufl) eqn:H20; try contradiction.
     cbn[Array.array] in H18.
     repeat straightline.
     { eexists; split.
       - split; auto.
         subst i.
         split. 1: admit.
         split; auto.
         exists (x1 + 1)%nat.
         split. 1: admit.
         replace ((x1+1)%nat) with (S x1) by blia.
         rewrite <- List.tl_skipn, H20.
         cbv [List.tl].
         assert (List.repeat (word.of_Z (word := parameters.word) (Ox "42")) (S x1) = List.repeat (word.of_Z (Ox "42")) x1 ++ [word.of_Z (Ox "42")]) by admit.
         rewrite H21.
         admit.
       - subst i v9.
         
     }
         
         replace (List.repeat (word.of_Z (Ox "42")) (S x1)) with ((List.repeat (word.of_Z (Ox "42")) x1) ++ [word.of_Z (Ox "42")]).
         Search List.repeat_cons.

         ecancel_assumption.
         List.repeat Array.array].
         
         ecancel_assumption.
         Search List.skipn.
         
         ecancel H16.

         
     Search List.skipn List.length.
     subst a8.
     straightline.
     eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
     
     

     refine ((atleastonce ["i"; "buffer"] (fun v T M I BUFFER =>
       v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m 
       
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
     { eexists; split; repeat straightline.
       subst i. rewrite word.unsigned_of_Z in H; inversion H. }
     { repeat (split; trivial; []).
       subst i. rewrite word.unsigned_of_Z.
       split.
       { discriminate. }
       split; trivial.
       eexists; split.
       { rewrite app_nil_l; trivial. }
       eexists; split.
       { constructor. }
       split.
       { constructor. }
       exact eq_refl. }
     repeat straightline.
     
     refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
       b = B /\ v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       lightbulb_spec.spi_write_full _ ^* th /\
       Z.of_nat (length th) + word.unsigned I = patience
       )) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
     
     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun v T M I BUFFER =>
       v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m
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
     {   repeat straightline. subst i.
         assert (br = word.of_Z 1). { subst br. reflexivity.
         change (word.unsigned (word.of_Z 1) = 0) in H11. 
     { move c6 at bottom. eexists; split; repeat straightline.
       subst i. rewrite word.unsigned_of_Z in H; inversion H. }
    
     
     hnf in c.
     
     let c := eval hnf in c in
         lazymatch c with
         | cmd.while _ _ => fail
         | cmd.cond _ _ _ => fail
         | cmd.interact _ _ _ => fail
         | _ => WeakestPrecondition.unfold1_cmd_goal; cbv beta match delta [cmd_body]
         end.

     current_trace_mem_locals.

     
     split; [auto|].
     split; [auto|].
     clear H9 H8 H7 H6 H5 H4 H3 H2 H1 H.
     subst v v0 v1 v2 v3 v4 v5 v6 v7 v8.
     repeat (rewrite word.unsigned_of_Z in H10).
     unfold word.wrap in H10.
     repeat (rewrite Zmod_small in H10 ;
             [|change width with 32; try apply stringHexBound; blia]).
     subst a a0 a1 a2 a3 a4 a5 a6 a7.
     cbv [message_val message_ok size_field offsets_field tags_field srep_val
                      List.fold_left snd fst List.map contents_offset tl
                      List.length tags_offset Nat.mul Nat.add stringToWord].
     cbv[Array.array].
     repeat (rewrite word_add_simplify).
     simpl.
     use_sep_assumption.
     simpl.
     cancel.
     simpl.
     cancel.
     cancel_seps_at_indices 9%nat 0%nat.
     Set Printing All.
     ecancel.
     Search (Lift1Prop.iff1 _ _ -> _).
     simpl.
     cancel.
     word_simplify.
     ecancel.
     cancel_seps_at_indices 9%nat 0%nat.
     simpl. Set Printing All. 
     unfold message_ok.
     subst a5.
     straightline_cleanup.
     
     match goal with | |- @WeakestPrecondition.store ?p access_size.four _ _ _ _ =>
      eapply (@Scalars.store_four_of_sep (@Semantics.width p) (@Semantics.word p) _ _ _ _ _) ; [solve[ecancel_assumption]|] end.
     straightline.
     replace buf with ([word.of_Z 4]++[word.of_Z 3]) in H. 2: admit.
     rewrite (iff1ToEq (array_append _ _ _ _ _)) in H.
     straightline.

     seprewrite_in (array_append scalar32 (word.of_Z 4) [word.of_Z 4] [word.of_Z 3]) H. 
     rewrite (array_append) in H.
     (* Start with header *)
     erewrite (array_index_nat_inbounds) in H.
     do 10 (destruct buf; [inversion H0|]).
     rewrite (array_append ) in H.
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

