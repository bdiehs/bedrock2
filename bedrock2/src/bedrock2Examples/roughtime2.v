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

    i = (constr:(40)); while (i < constr:(104)) {
      store4(buffer + i, constr:(Ox"42"));
      i = (i + constr:(4))
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

  Definition sig_val : list (@word.rep 32 (@parameters.word p)). Admitted.
  
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

   Ltac word_simplify' :=
      repeat match goal with | |- context [?a + ?b] => progress (ring_simplify (a + b)) end;
      repeat match goal with | |- context [word.sub ?a ?b] => progress (ring_simplify (word.sub a b)) end;
      repeat match goal with | |- context [ (word.unsigned (word.of_Z ?z))] => rewrite (word.unsigned_of_Z z); replace (word.wrap z) with z by (cbn; blia) end;
      repeat match goal with | |- context [word.of_Z (word.unsigned ?z)] => rewrite (word.of_Z_unsigned z) end;
      repeat match goal with | H: context [?a + ?b] |- _ => progress (ring_simplify (a + b) in H) end;
      repeat match goal with | H: context [word.sub ?a ?b] |- _ => progress (ring_simplify (word.sub a b) in H) end;
      repeat match goal with | H: context [word.unsigned (word.of_Z ?z)] |- _ => rewrite (word.unsigned_of_Z z) in H; replace (word.wrap z) with z in H by (cbn; blia) end;
      repeat match goal with | H: context [word.of_Z (word.unsigned ?z)] |- _ => rewrite (word.of_Z_unsigned z) in H  end.
   

   Ltac word_unsigned z := rewrite (word.unsigned_of_Z z); replace (word.wrap z) with z by (cbn; blia).


   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     do 10 (destruct buf; [inversion H0|]).
     inversion H0; clear H0.
     cbn[Array.array] in H.

     word_simplify'.
     repeat straightline.
     subst_words.
     clear H9 H8 H7 H6 H5 H4 H3 H1 H0 H.
     word_simplify'.

     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       exists i, (i < 16)%nat /\ V = 64 - 4 * (Z.of_nat i) /\
       I = word.of_Z (40 + 4 * Z.of_nat i) /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + I) (List.skipn i buf) *
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
       split; try split; try split; try split; auto; try blia.
       cbn [List.repeat Array.array List.skipn].
       ecancel_assumption. }
     repeat straightline.
     subst_words.
     assert (List.length (List.skipn x1 buf) <> 0%nat).
     { rewrite List.skipn_length; blia. }
     destruct (List.skipn x1 buf) eqn:H17; try contradiction.
     array_app_cons_sep.
     repeat straightline.
     { subst_words.
       eexists; auto.
       split.
       - exists (x1 + 1)%nat.
         split.
         { word_simplify.
           destruct (word.ltu (word.mul (lit 4) (lit (Z.of_nat x1)) + lit 44) (lit 104)) eqn:H5.
           2: { rewrite word.unsigned_of_Z in H3; contradiction. }
           rewrite word.unsigned_ltu, word.unsigned_of_Z in H5.
           admit. }
         split; auto.
         split; try split; try split; auto.
         { rewrite Nat2Z.inj_add; do 2 word_simplify; auto. }
         use_sep_assumption.
         cancel.
         cancel_seps_at_indices 2%nat 1%nat.
         { do 2 word_simplify.
           f_equal.
           admit. }
         repeat word_simplify.
         match goal with
         | |- context [List.repeat ?x (?n + 1)] =>
           replace (List.repeat x (n + 1)) with (List.repeat x n ++ [x])
         end.
         { array_app_cons_sep.
           rewrite List.repeat_length.
           change (Ox"42") with 66.
           cbn[seps].
           repeat word_simplify.
           cancel. }
         admit.
       - rewrite Nat2Z.inj_add.
         blia.
     }
     
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

