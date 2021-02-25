
Require Import bedrock2.Array bedrock2.Scalars bedrock2.SepLogAddrArith.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import bedrock2.Syntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation coqutil.Z.Lia.
Require Import Coq.Strings.Ascii.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type :=
  String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.


Fixpoint N_of_string (s : string) : N :=
  match s with
  | EmptyString => 0
  | String a s => (N_of_ascii a) + 256 * (N_of_string s)
  end.

Definition Z_of_string (s : string) := Z.of_N (N_of_string s).

Lemma stringHexBound : forall s, (length s <= 4)%nat -> 0 <= Z_of_string s < 2^32.
Proof.
  intros s.
Admitted.

Opaque Z_of_string.

Definition createTimestampMessage :=
  let buffer := "buffer" in
  let i := "i" in
  ("createTimestampMessage", ([buffer], []:list String.string, bedrock_func_body:(
    store4(buffer, coq:(Ox"5"));
    store4(buffer + coq:(4), coq:(Ox"40"));
    store4(buffer + coq:(8), coq:(Ox"40"));
    store4(buffer + coq:(12), coq:(Ox"a4"));
    store4(buffer + coq:(16), coq:(Ox"13c"));

    store4(buffer + coq:(20), coq:(Z_of_string "SIG"));
    store4(buffer + coq:(24), coq:(Z_of_string "PATH"));
    store4(buffer + coq:(28), coq:(Z_of_string "SREP"));
    store4(buffer + coq:(32), coq:(Z_of_string "CERT"));
    store4(buffer + coq:(36), coq:(Z_of_string "INDX"));

    i = (coq:(64)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(100) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(104), coq:(Ox"3"));
    store4(buffer + coq:(108), coq:(Ox"4"));
    store4(buffer + coq:(112), coq:(Ox"c"));

    store4(buffer + coq:(116), coq:(Z_of_string "RADI"));
    store4(buffer + coq:(120), coq:(Z_of_string "MIDP"));
    store4(buffer + coq:(124), coq:(Z_of_string "ROOT"));
    
    store4(buffer + coq:(128), coq:(Ox"42"));
    store4(buffer + coq:(132), coq:(Ox"4242"));
    i = (coq:(64)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(200) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(204), coq:(Ox"2"));
    store4(buffer + coq:(208), coq:(Ox"40"));
    store4(buffer + coq:(212), coq:(Z_of_string "SIG"));
    store4(buffer + coq:(216), coq:(Z_of_string "DELE"));
    i = (coq:(64)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(280) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(284), coq:(Ox"3"));
    store4(buffer + coq:(288), coq:(Ox"20"));
    store4(buffer + coq:(292), coq:(Ox"28"));

    store4(buffer + coq:(296), coq:(Z_of_string "PUBK"));
    store4(buffer + coq:(300), coq:(Z_of_string "MINT"));
    store4(buffer + coq:(304), coq:(Z_of_string "MAXT"));
 
    i = (coq:(48)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(352) - i, coq:(Ox"42"))
    }))).
    
Require Import bedrock2.ToCString.
   Definition allProgsAsCString : string :=
     Eval cbv in c_module [createTimestampMessage].
   Print allProgsAsCString.

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

  Definition entry : Type := string * Semantics.word * (Semantics.word -> mem -> Prop).
  
  Infix "*" := (sep).
  Infix "*" := (sep) : type_scope.

  Local Infix "^+" := word.add  (at level 50, left associativity).
  Local Infix "^-" := word.sub  (at level 50, left associativity).
  Local Infix "^*" := word.mul  (at level 50, left associativity).
  Local Notation "/_" := word.of_Z.      (* smaller angle: squeeze a Z into a word *)
  Local Notation "\_" := word.unsigned.  (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
  

  Notation array32 := (array scalar32 (word.of_Z 4)).
  
  Definition stringToWord (s : string) := word.of_Z (Z_of_string s).

  Definition size_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    scalar32 addr (/_ (Z.of_nat (List.length entries))).
  
  Definition offsets_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr ^+ (word.of_Z 4)) 
            (List.map (fun entry => (snd (fst entry))) (tl entries)).
  
  Definition tags_offset (entries : list entry) :=
    (4 + 4 * (List.length (tl entries)))%nat.
  
  Definition tags_field (addr: Semantics.word) (entries : list entry) : mem -> Prop :=
    array32 (addr ^+ (word.of_Z (Z.of_nat (tags_offset entries))))
            (List.map (fun entry => stringToWord (fst (fst entry))) entries).

  Definition contents_offset (entries : list entry) :=
    (tags_offset entries + 4 * (List.length entries))%nat.
  
  Definition message_ok (addr: Semantics.word) (entries : list entry): mem -> Prop :=
    size_field addr entries * offsets_field addr entries * tags_field addr entries *
    let current_addr := addr ^+ (word.of_Z (Z.of_nat (contents_offset entries))) in
    List.fold_left (fun P entry => (snd entry) (current_addr ^+ (snd (fst entry))) * P)
                   entries (emp True).
  
  Definition repeat_dummy n := fun addr => array32 (addr: Semantics.word) (List.repeat (/_ (Ox"4242")) n).


  Definition srep_val : list entry :=
    [("RADI", word.of_Z 0, repeat_dummy 1);
    ("MIDP", word.of_Z 4,  repeat_dummy 2);
    ("ROOT", word.of_Z 12, repeat_dummy 64)
    ].

  Definition dele_val : list entry :=
    [("MINT", word.of_Z 0, repeat_dummy 8);
    ("MAXT", word.of_Z 32, repeat_dummy 8);
    ("PUBK", word.of_Z 40, repeat_dummy 64)
    ].

  Definition cert_val : list entry :=
    [("SIG", word.of_Z 0, repeat_dummy 64);
    ("DELE", word.of_Z 64, fun addr => message_ok addr dele_val)
    ].
  
  
  Definition message_val : list entry :=
    [("SIG", word.of_Z 0, fun addr => (array32 addr (List.repeat (/_ (Ox"42")) 64)));
    ("PATH", word.of_Z 64, fun _ => (emp True));
    ("SREP", word.of_Z 64, fun addr => message_ok addr srep_val);
    ("CERT", word.of_Z 164, fun addr => message_ok addr cert_val);
    ("INDX", word.of_Z 316, fun addr => (array32 addr (List.repeat (/_ (Ox"42")) 64)))
    ].
    

  Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" := fun functions =>
    forall p_addr buf R m t,
      ((array32 p_addr buf) * R) m ->
      List.length buf = 352%nat ->
      WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr]
      (fun t' m' rets => t = t' /\ rets = nil /\ (message_ok p_addr message_val * R) m'). 
  
   Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
  
   Ltac subst_words :=
     repeat match goal with x := _ : word.rep |- _ => subst x end.
   
   Notation "a |-> v" := (scalar32 a (/_ v)) (at level 30).
   Notation "l [[ n  |:= v ]]" := (List.listUpdate l n v) (left associativity, at level 50).

   Ltac word_simplify :=
       match goal with
       | |- context [?a ^+ ?b] => progress (ring_simplify (a ^+ b))
       | |- context [?a ^- ?b] => progress (ring_simplify (a ^- b))
       end.

   Ltac word_Z_unsigned :=
     match goal with
     | |- context [\_ (/_ ?z)] => rewrite (word.unsigned_of_Z z); change (word.wrap z) with z
     | |- context [/_ (\_ ?z)] => rewrite (word.of_Z_unsigned z)
     end.

   Ltac word_simplify_in H :=
       match type of H with 
       | context [?a ^+ ?b] => progress (ring_simplify (a ^+ b) in H)
       | context [?a ^- ?b] => progress (ring_simplify (a ^- b) in H)
       end.
   Ltac word_Z_unsigned_in H:=
     match type of H with
     | context [\_ (/_ ?z)] => rewrite (word.unsigned_of_Z z) in H; change (word.wrap z) with z in H
     | context [/_ (\_ ?z)] => rewrite (word.of_Z_unsigned z) in H
     end.

   Ltac word_unwrap t :=
     unfold word.wrap; rewrite (Zmod_small t); [| assert (0 <= t < 2^width) by blia; assumption].

   Ltac word_unwrap_in t H :=
     unfold word.wrap in H; rewrite (Zmod_small t) in H; [| assert (0 <= t < 2^width) by blia; assumption].

   Definition todo : False. Admitted.

   Ltac subst_nat :=
     match goal with
     | H : @eq nat ?x ?y |- context[?x] => rewrite H
     end.
(*
   Ltac array_straightline :=
     match goal with
     | x : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' ?v _ => match p with context [array32 ?addr ?xs] =>
       remember (Z.to_nat ((\_ (addr' ^- addr)) / 4)) as n eqn:Heqn;
       ring_simplify (addr' ^- addr) in Heqn;
       word_Z_unsigned_in Heqn;
       cbv in Heqn; (*Dangerous*)
       assert (List.length (xs [[n |:= v]]) = 1024%nat) by (rewrite List.listUpdate_length; blia);
       eapply (array_store_four_of_sep_32bit _ addr addr' n xs _ (word.of_Z 4)); subst ;[try word_Z_unsigned; try ring | ecancel_assumption | subst_nat; blia |]
 end
     end.

   Ltac array_first_cleanup H :=
     rewrite List.skipn_skipn in H;
  *)   
   
   Ltac skipn_simpl :=
     match goal with
     | H : context [List.skipn ?a (List.skipn ?b ?l)] |- _ =>
       rewrite List.skipn_skipn in H;
         cbn[Nat.add] in H
     end.

   
   Ltac array_first_straightline :=
     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ access_size.four ?m ?addr' _ _ =>
       match p with
         context [array32 ?addr ?xs] =>
         subst_words;
         try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H);
         array_app_cons_sep;
         try word_simplify_in H;
         eapply array_first_store_four_of_sep_32bit;
         [ reflexivity | ecancel_assumption | try rewrite skipn_length; blia |];
         repeat straightline
       end
     end.

   Ltac array_first_before :=
     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ access_size.four ?m ?addr' _ _ =>
       subst_words;
       eapply array_first_store_four_of_sep_32bit;
       [ reflexivity | ecancel_assumption | try rewrite skipn_length; blia |];
       array_app_cons_sep;
       repeat straightline
     end.
   
   Ltac array_first_after :=
     match goal with
     | H : context [array32 (word.add ?a ?b) (List.skipn ?m ?l)] |- _ =>
       ring_simplify (word.add a b) in H;
       try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H)
     end.
   
   Ltac array_first_straightline' := array_first_before; array_first_after.

   Ltac subst_skipn :=
     match goal with
     | H : context [List.skipn ?n ?buf] |- _ =>
       match goal with
       | H' : List.length ?buf = ?l |- _ =>
         is_var buf;
         let buf' := fresh buf in
         let H0 := fresh H in
         let H1 := fresh H in
         remember (List.skipn n buf) as buf' eqn:H0;
         pose proof (H1 := f_equal (@List.length _) H0);
         rewrite skipn_length, H' in H1;
         cbn[Nat.sub] in H1;
         clear H' H0 buf;
         rename buf' into buf
       end
     end.

   Ltac array_straightline :=
     match goal with
     | x : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' ?v _ =>
       match p with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep' _ addr addr' xs);
         [ecancel_assumption |];
         ring_simplify (addr' ^- addr);
         word_Z_unsigned;
         progress cbv zeta;
         split; [try reflexivity | split; [simpl (Z.to_nat _); try blia|] ]
       end
     end.
   
   (*Ideally I want to do context on two terms inside one hypothesis*)
   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     eapply (array_store_four_of_sep' _); [ecancel_assumption|].
     
     ring_simplify (p_addr ^- p_addr).
     word_Z_unsigned.
     ring_simplify (0 / 4).
     match goal with
     | |- context [Z.to_nat (?a / 4)] =>
       let r := isZcst a in
       lazymatch r with | true =>
         let x := eval cbv in (Z.to_nat (a/4)) in change (Z.to_nat (a/4)) with x
       end;
       idtac a r
     end.
     simpl (Z.to_nat _).
     rewrite 
     
     Search word.of_Z word.unsigned.
     
     
     word_Z_unsigned.
     cbv zeta.
     word_Z_unsigned.
     split; [reflexivity|].
     
     split.
     match goal with
     | x : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' ?v _ =>
       match p with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep' _ addr addr' xs);
         [ecancel_assumption |];
         ring_simplify (addr' ^- addr);
         cbv zeta
       end
     end.

     array_straightline.
     eapply (array_store_four_of_sep' _ _ _ _); [ecancel_assumption|].
     ring_simplify term+
     cbv zeta.
     
     
     array_straightline.
     array_straightline; ring_simplify (p_addr ^- p_addr).
     
     array_straightline.
     { ring_simplify (p_addr ^- p_addr). word_Z_unsigned. reflexivity. }
     { admit. }
     cbv zeta.
                         
     eapply array_store_four_of_sep'; [reflexivity| ecancel_assumption| |].
     { word_simplify. word_Z_unsigned. 
     
     
     
     assert (Datatypes.length buf = 352%nat) by blia; clear H0.
     do 10 array_first_straightline'.
     clear H9 H8 H7 H6 H5 H4 H3 H2 H0 H.
     subst_skipn.
     remember ((p_addr ^+ /_ 36) |-> Z_of_string "INDX" *
         ((p_addr ^+ /_ 32) |-> Z_of_string "CERT" *
          ((p_addr ^+ /_ 28) |-> Z_of_string "SREP" *
           ((p_addr ^+ /_ 24) |-> Z_of_string "PATH" *
            ((p_addr ^+ /_ 20) |-> Z_of_string "SIG" *
             ((p_addr ^+ /_ 16) |-> 316 *
              ((p_addr ^+ /_ 12) |-> 164 *
               ((p_addr ^+ /_ 8) |-> 64 * ((p_addr ^+ /_ 4) |-> 64 * (p_addr |-> 5 * R)))))))))%type) as P.
     assert ((P * array32 (p_addr ^+ /_ 40) buf) m9) by (rewrite HeqP; ecancel_assumption).
     clear H10.
     subst i.     

     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (104 - V))) (List.skipn i buf) * P * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (P * array32 (p_addr ^+ /_ 40) (List.repeat (word.of_Z (Ox"42")) 16) * array32 (p_addr ^+ (/_ (104))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
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
       split; [auto| split; [word_Z_unsigned; blia| split; [auto|] ] ] .
       simpl (104 - _).
       cbn [List.repeat Array.array List.skipn List.map].
       ecancel_assumption. }
     { repeat straightline.
       2: {
         split; try split; auto.
         replace x2 with 16%nat in H0, H4 by blia.
         simpl in H0.
         rewrite H0 in *.
         simpl (104-0) in H4.
         ecancel_assumption. }
       
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H4.
       word_Z_unsigned_in H4.
       pose proof (word.unsigned_range x0).
       assert (List.length (List.skipn x2 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x2 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x2)%nat.
         replace (64 - 4 * Z.of_nat (1 + x2)) with (60 - 4 * Z.of_nat x2) by blia.
         split; auto.
         split; [|split; [auto|] ].
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x0 - 4).
           blia.
         }
         { pose proof (f_equal word.of_Z H0).
           word_Z_unsigned_in H8.
           rewrite H8 in H7.
           cbn[Nat.add List.repeat].
           rewrite repeat_cons.
           array_app_cons_sep.
           rewrite repeat_length, <- List.tl_skipn, H17.
           cbn[List.tl].
           repeat word_simplify.
           repeat word_simplify_in H7.
           change (66) with (Ox "42") in H7.
           ecancel_assumption. }
       }
       split; [blia| auto].
     }
     repeat straightline.
     clear H.
     do 8 array_first_straightline'.
     clear H7 H6 H5 H4 H3 H1 H0 H.
     repeat straightline.
     subst i.
     subst_skipn.

     remember ((p_addr ^+ /_ 132) |-> 16962 *
        ((p_addr ^+ /_ 128) |-> 66 *
         ((p_addr ^+ /_ 124) |-> Z_of_string "ROOT" *
          ((p_addr ^+ /_ 120) |-> Z_of_string "MIDP" *
           ((p_addr ^+ /_ 116) |-> Z_of_string "RADI" *
            ((p_addr ^+ /_ 112) |-> 12 *
             ((p_addr ^+ /_ 108) |-> 4 *
              ((p_addr ^+ /_ 104) |-> 3 *
               (P * array32 (p_addr ^+ /_ 40) (repeat (/_ (Ox "42")) 16)))))))))%type) as Q.
     assert ((Q * array32 (p_addr ^+ /_ 136) buf) m7) by (rewrite HeqQ; ecancel_assumption).
     clear H8.

     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 136)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (200 - V))) (List.skipn i buf) * Q * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (Q * array32 (p_addr ^+ /_ 136) (List.repeat (word.of_Z (Ox"42")) 16) * array32 (p_addr ^+ (/_ (200))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
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
       split; [auto| split; [word_Z_unsigned; blia| split; [auto|] ] ] .
       simpl (200 - _).
       cbn [List.repeat Array.array List.skipn List.map].
       ecancel_assumption. }
     { repeat straightline.
       2: {
         split; try split; auto.
         replace x3 with 16%nat in H0, H4 by blia.
         simpl in H0.
         rewrite H0 in *.
         simpl (200-0) in H4.
         ecancel_assumption. }
       
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H4.
       word_Z_unsigned_in H4.
       pose proof (word.unsigned_range x1).
       assert (List.length (List.skipn x3 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x3 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x3)%nat.
         replace (64 - 4 * Z.of_nat (1 + x3)) with (60 - 4 * Z.of_nat x3) by blia.
         split; auto.
         split; [|split; [auto|] ].
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x1 - 4).
           blia.
         }
         { pose proof (f_equal word.of_Z H0).
           word_Z_unsigned_in H8.
           rewrite H8 in H7.
           cbn[Nat.add List.repeat].
           rewrite repeat_cons.
           array_app_cons_sep.
           rewrite repeat_length, <- List.tl_skipn, H17.
           cbn[List.tl].
           repeat word_simplify.
           repeat word_simplify_in H7.
           change (66) with (Ox "42") in H7.
           ecancel_assumption. }
       }
       split; [blia| auto].
     }
     repeat straightline.
     clear H.
     do 4 array_first_straightline'.
     clear H3 H2 H0 H.
     repeat straightline.
     subst i.
     subst_skipn.

     remember ((p_addr ^+ /_ 212) |-> Z_of_string "DELE" *
        ((p_addr ^+ /_ 208) |-> Z_of_string "SIG" *
         ((p_addr ^+ /_ 204) |-> 64 *
          ((p_addr ^+ /_ 200) |-> 2 *
           (Q * array32 (p_addr ^+ /_ 136) (repeat (/_ (Ox "42")) 16)))))) as P1.
     assert ((P1 * array32 (p_addr ^+ /_ 216) buf) m3) by (rewrite HeqP1; ecancel_assumption).
     clear H4.

     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 216)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (280 - V))) (List.skipn i buf) * P1 * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (P1 * array32 (p_addr ^+ /_ 216) (List.repeat (word.of_Z (Ox"42")) 16) * array32 (p_addr ^+ (/_ (280))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
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
       split; [auto| split; [word_Z_unsigned; blia| split; [auto|] ] ] .
       simpl (280 - _).
       cbn [List.repeat Array.array List.skipn List.map].
       ecancel_assumption. }
     { repeat straightline.
       2: {
         split; try split; auto.
         replace x4 with 16%nat in H0, H4 by blia.
         simpl in H0.
         rewrite H0 in *.
         simpl (280-0) in H4.
         ecancel_assumption. }
       
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H4.
       word_Z_unsigned_in H4.
       pose proof (word.unsigned_range x2).
       assert (List.length (List.skipn x4 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x4 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x4)%nat.
         replace (64 - 4 * Z.of_nat (1 + x4)) with (60 - 4 * Z.of_nat x4) by blia.
         split; auto.
         split; [|split; [auto|] ].
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x2 - 4).
           blia.
         }
         { pose proof (f_equal word.of_Z H0).
           word_Z_unsigned_in H8.
           rewrite H8 in H7.
           cbn[Nat.add List.repeat].
           rewrite repeat_cons.
           array_app_cons_sep.
           rewrite repeat_length, <- List.tl_skipn, H17.
           cbn[List.tl].
           repeat word_simplify.
           repeat word_simplify_in H7.
           change (66) with (Ox "42") in H7.
           ecancel_assumption. }
       }
       split; [blia| auto].
     }
     repeat straightline.
     clear H.
     do 6 array_first_straightline'.
     clear H5 H4 H3 H1 H0 H.
     repeat straightline.
     subst i.
     subst_skipn.

     remember ((p_addr ^+ /_ 300) |-> Z_of_string "MAXT" *
        ((p_addr ^+ /_ 296) |-> Z_of_string "MINT" *
         ((p_addr ^+ /_ 292) |-> Z_of_string "PUBK" *
          ((p_addr ^+ /_ 288) |-> 40 *
           ((p_addr ^+ /_ 284) |-> 32 *
            ((p_addr ^+ /_ 280) |-> 3 *
             (P1 * array32 (p_addr ^+ /_ 216) (repeat (/_ (Ox "42")) 16)))))))%type) as P2.
     assert ((P2 * array32 (p_addr ^+ /_ 304) buf) m5) by (rewrite HeqP2; ecancel_assumption).
     clear H6.
     
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 48 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 304)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (352 - V))) (List.skipn i buf) * P2 * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (P2 * array32 (p_addr ^+ /_ 304) (List.repeat (word.of_Z (Ox"42")) 12) * array32 (p_addr ^+ (/_ (352))) (List.skipn 12%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
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
       split; [auto| split; [word_Z_unsigned; blia| split; [auto|] ] ] .
       simpl (352 - _).
       cbn [List.repeat Array.array List.skipn List.map].
       ecancel_assumption. }
     { repeat straightline.
       2: {
         split; try split; auto.
         replace x5 with 12%nat in H0, H4 by blia.
         simpl in H0.
         rewrite H0 in *.
         simpl (352-0) in H4.
         ecancel_assumption. }
       
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H4.
       word_Z_unsigned_in H4.
       pose proof (word.unsigned_range x3).
       assert (List.length (List.skipn x5 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x5 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x5)%nat.
         split; auto.
         split; [|split; [auto|] ].
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x3 - 4).
           blia.
         }
         { pose proof (f_equal word.of_Z H0).
           word_Z_unsigned_in H8.
           rewrite H8 in H7.
           cbn[Nat.add List.repeat].
           rewrite repeat_cons.
           array_app_cons_sep.
           rewrite repeat_length, <- List.tl_skipn, H17.
           cbn[List.tl].
           replace (Z.of_nat (S x5)) with (1 + Z.of_nat x5) by blia. 
           repeat word_simplify.
           repeat word_simplify_in H7.
           change (66) with (Ox "42") in H7.
           ecancel_assumption. }
       }
       split; [blia| auto].
     }
     repeat straightline.
     clear H.
     array_first_straightline'.
     clear H3.
     straightline.
     split; [auto| split; [auto| ] ].
     subst P2 P1 Q P.

     unfold message_val, srep_val, cert_val, dele_val, message_ok.
     unfold size_field, offsets_field, tags_field, tags_offset.
     cbn[List.length tl map fst snd Array.array Z.of_nat].
     simpl (Z.of_nat _).
     unfold fold_left.
     cbn[fst snd].
     unfold repeat_dummy.
     simpl (Z.pos _).
     repeat word_simplify.
     ecancel_assumption.
   Qed.
     (*
     remember 
     
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"]) * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (array32 p_addr (List.map word.of_Z ([5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"] ++ (List.repeat (Ox"42") 16))) * array32 (p_addr ^+ (/_ (104))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist

           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
     
     
     array_first_straightline'.
     array_first_straightline'.
     array_first_before.
     array_first_after.
     
     array_first_straightline'.
     array_first_after.
     array_first_before.
      match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ access_size.four ?m ?addr' _ _ =>
       eapply array_first_store_four_of_sep_32bit;
       [ reflexivity | ecancel_assumption | try rewrite skipn_length; blia |];
       repeat straightline
      end.
      array_app_cons_sep.
     match goal with
     | H : context [array32 (word.add ?a ?b) (List.skipn ?m ?l)] |- _ =>
       ring_simplify (word.add a b);
       try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H);
       array_app_cons_sep
     end.
     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ access_size.four ?m ?addr' _ _ =>
       eapply array_first_store_four_of_sep_32bit;
       [ reflexivity | ecancel_assumption | try rewrite skipn_length; blia |];
       repeat straightline
     end.
     do 10 array_first_straightline.
     array_app_cons_sep.
     array_first_straightline.

     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' _ _ =>
       match p with
         context [array32 ?addr ?xs] =>
         try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H);
         array_app_cons_sep;
         try word_simplify_in H;
         eapply (array_first_store_four_of_sep_32bit _ addr xs _ (word.of_Z 4));
         [ ecancel_assumption | try rewrite skipn_length; blia |];
         repeat straightline
       end
     end.

     lazymatch goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' _ _ =>
       lazymatch p with
         context [array32 ?addr ?xs] =>
         subst_words;
         try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H);
         array_app_cons_sep;
         try word_simplify_in H;
         eapply array_first_store_four_of_sep_32bit;
         [ reflexivity | ecancel_assumption | try rewrite skipn_length; blia |];
         repeat straightline
       end
     end.
     eapply (array_first_store_four_of_sep_32bit _ _ _ _ _);
         [ ecancel_assumption | try rewrite skipn_length; blia |].
     subst_words.
     
     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' _ _ =>
       match p with
         context [array32 ?addr ?xs] =>
         repeat straightline; try (rewrite List.skipn_skipn in H; cbn[Nat.add] in H);
         array_app_cons_sep;
         try word_simplify_in H;
         idtac p
       end
     end.
     
     
     array_first_straightline.
     
     array_first_straightline.
     
     try rewrite List.skipn_skipn in H0.
     array_app_cons_sep.
     
     array_first_straightline.
     try (rewrite List.skipn_skipn in H2; cbn[Nat.add] in H2).
     array_app_cons_sep.
     word_simplify_in H2.
     array_first_straightline.
     
     cbn[Nat.add] in H2.
     
     repeat straightline.
     subst_words.
     array_app_cons_sep.

     array_first_straightline.
     match goal with
     | H : context [List.skipn ?a (List.skipn ?b ?l)] |- _ =>
       rewrite List.skipn_skipn in H;
         cbn[Nat.add] in H
     end.
     
     
     rewrite List.skipn_skipn.
     change (1 + 1)%nat with 2%nat.
     repeat straightline.
     subst_words.
     array_app_cons_sep.
     word_simplify_in H2.

     array_first_straightline.
     repeat straightline.
     rewrite List.skipn_skipn in H3.
     array_app_cons_sep.
     word_simplify_in H3.
     
     
     
     
     do 10 (array_straightline; repeat straightline; subst_words).

     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr ^+ (/_ 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr ^+ (/_ (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"]) * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (array32 p_addr (List.map word.of_Z ([5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"] ++ (List.repeat (Ox"42") 16))) * array32 (p_addr ^+ (/_ (104))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist

           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
     
     straightline.
     
     match goal with
     | H : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' _ _ => match p with | context [array32 ?addr ?xs] => idtac xs
                                                                                        end
     end.
     match type of H0 with
     | ((?a * ((?c * ?e) * ?d)) * ?b) ?m => assert (seps [a; b; c; d; e] m)
     end.
     { unfold seps; ecancel_assumption. }

     Ltac pick_nat n :=
       multimatch n with
       | S ?m => constr:(m)
       | S ?m => pick_nat m
       end.
     
     try match goal with
     | H : (seps ?l ?m) |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' _ _ =>
       (*remember (Z.to_nat ((\_ (addr' ^- addr)) / 4)) as n eqn:Heqn;
       ring_simplify (addr' ^- addr) in Heqn;
       word_Z_unsigned_in Heqn;
       simpl in Heqn; *)

       (*Make an array lemma with following precondition*)
       assert (exists i addr ws, nth_error l i = Some (array32 addr ws) /\
         let n := Z.to_nat (\_(addr' ^- addr) / 4) in (n < List.length ws)%nat);
         [let L := eval cbv[List.length] in (List.length l) in let r := pick_nat L in exists r; idtac r; fail |]
       
       (*eapply (array_store_four_of_sep addr addr' n xs _ (word.of_Z 4))*)
(* subst ;[try ring | try rewrite List.skipn_length; blia | ecancel_assumption|]*)
     end.
     
     Ltac pick_nat n :=
       multimatch n with
       | S ?m => constr:(m)
       | S ?m => pick_nat m
       end.

     { (*Pattern to use in array_straightline*)
       
       try let r := pick_nat 3%nat in solve[exists r].
     
     array_straightline.
     repeat straightline.
     clear H0.
     rewrite firstn_O, app_nil_l in H.
     array_app_cons_sep.
     cbn [List.length] in H.
     word_simplify_in H.
     rewrite truncate_word_nop_32bit, List.skipn_skipn in H by auto.
     subst_words.
     change (1 + 0 + 1)%nat with 2%nat in H.
     array_straightline.
     repeat straightline.
     match goal with
     | x : context [array32 ?addr ?xs] |- @WeakestPrecondition.store _ Syntax.access_size.four _ ?addr' _ _ =>
       remember (Z.to_nat ((\_ (addr' ^- addr)) / 4)) as n eqn:Heqn;
       ring_simplify (addr' ^- addr) in Heqn;
       word_Z_unsigned_in Heqn;
       simpl in Heqn;
       eapply (Scalars.store_array_of_sep addr addr' n xs _ (word.of_Z 4)); subst ;[try ring | try rewrite List.skipn_length; blia | ecancel_assumption|]
     end.
     { rewrite List.skipn_length.
     array_straightline.
     match goal with
     | x : context [array32 ?addr ?xs] |- @WeakestPrecondition.store _ Syntax.access_size.four _ ?addr' _ _ =>
       remember (Z.to_nat ((\_ (addr' ^- addr)) / 4)) as n eqn:Heqn;
       ring_simplify (addr' ^- addr) in Heqn;
       word_Z_unsigned_in Heqn;
       simpl in Heqn;
       eapply (Scalars.store_array_of_sep addr addr' n xs _ (word.of_Z 4)); subst 
     end.
     remember
     3: { eapply H. eassumption.
     
     eapply store_array_of_sep.
     array_straightline.
     match goal with
     | x : context [(array32 ?addr ?xs * ?R) ?m] |- @WeakestPrecondition.store _ Syntax.access_size.four _ ?addr' _ _ =>
       remember (Z.to_nat ((\_ (addr' ^- addr)) / 4)) as n;
       ring_simplify (addr' ^- addr) in Heqn;
       word_Z_unsigned_in Heqn;
       simpl in Heqn;
       eapply (Scalars.store_array_of_sep addr addr' n xs _ (word.of_Z 4)); subst ;[try ring | try blia | eassumption|]
     end.
     { blia. ring. ring_simplify (p_addr ^- p_addr).
       
       ring_simplify (/_ (\_ (/_ 4) * Z.of_nat (Z.to_nat (\_ (/_ 0) / 4)))). simpl.
       ring. ring_simplify (p_addr ^+ /_ (\_ (/_ 4) * Z.of_nat 0)).
     array_straightline.
     { repeat word_simplify.
       repeat word_Z_unsigned.
       change (0 / 4) with 0.
       rewrite Z2Nat.id by blia.
       ring. }
       simpl.
       replace (word.mul (word.of_Z 4) (word.of_Z 0)) with (word.of_Z 0).
       2: { reflexivity.
       word_Z_unsigned.
     { word_simplify.
      eapply (Scalars.store_array_of_sep p_addr p_addr (Z.to_nat (word.unsigned (word.sub p_addr p_addr) / 4)) buf).
     match goal with
     | x : context [(array32 ?addr ?xs * ?R) ?m] |- @WeakestPrecondition.store _ Syntax.access_size.four _ ?addr' _ _ => eapply (Scalars.store_array_of_sep addr addr' (word.divu (word.sub addr' addr) (word.of_Z 4)) xs); [| try ring | try blia |]
     end.
     array_straightline.
     match goal with
     | x : context [(array32 ?addr ?xs * ?R) ?m] |- @WeakestPrecondition.store _ Syntax.access_size.four _ ?addr' _ _ => eapply (Scalars.store_array_of_sep (word.sub addr' addr) _ _ xs); [| try ring | try blia |]
     end.
     array_solve.
     eapply (store_array_of_sep p_addr _ 0%nat buf _ _);
       [ring | blia | eassumption |].
     repeat straightline.
     rewrite firstn_O, app_nil_l in H0. 
     array_app_cons_sep.
     word_simplify_in H0.
     simpl in H0.
     eapply (store_array_of_sep p_addr _ 0%nat _ _ (word.of_Z 4));
       [ring | blia | eassumption |].
     
     
     unfold Array.array in H.
     unfold WeakestPrecondition.store.
     
     straightline.
     
     cbn[Array.array] in H.
     (* Make a helper lemma that says what happens if I set a value inside an array 
        straightline can invoke such lemma:


  Lemma store_four_of_sep addr (oldvalue : word32) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr (word.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.

(* Ideally I would be able to compute n and not have to specify it *)
Lemma store_four_of_sep addr (oldvalues : list word32) (value : word) R m (post:_->Prop) (_ : addr' = addr + size * n) (_ : n < length oldvalues)
    (Hsep : sep (array32 addr oldvalues) R m)
    (Hpost : forall m, sep (array32 addr oldvalues[n |-> value]) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m (addr') value = Some m1 /\ post m1.

Conclusion: Weakestprecondition.store access_size.four m p_addr v post


      *)

     
     ring_simplify (p_addr + lit 4 + lit 4 + lit 4 + lit 4 + lit 4 + lit 4 + lit 4 +
                    lit 4 + lit 4 + lit 4).
     (word_simplify_in H).
     Eval cbn in (lit (4 + 4)).
     (word_simplify_in H).
     (word_simplify_in H).
     (word_simplify_in H).
     (word_simplify_in H).
     (word_simplify_in H).
     (word_simplify_in H).
     
     
     repeat straightline.
     subst_words.
     clear H9 H8 H7 H6 H5 H4 H3 H1 H0 H.
     repeat word_Z_unsigned_in H10.
       
     
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"]) * R) M) (fun t m i buff => t = T /\ buff = p_addr /\ (array32 p_addr (List.map word.of_Z ([5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"] ++ (List.repeat (Ox"42") 16))) * array32 (p_addr + (lit (104))) (List.skipn 16%nat buf) * R) m))) _ _ _ _ _ _ _);
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
     { exists 0%nat.
       split; auto.
       split; try word_Z_unsigned; try split; try split; try blia; auto.
       word_simplify.
       cbn [List.repeat Array.array List.skipn List.map].
       change (Z_of_string "SIG") with 4671827.
       change (Z_of_string "PATH") with 1213481296.
       change (Z_of_string "SREP") with 1346720339.
       change (Z_of_string "CERT") with 1414677827.
       change (Z_of_string "INDX") with 1480871497.
       repeat word_simplify.
       ecancel_assumption. }
     { repeat straightline.
       2: {
         split; try split; auto.
         replace x2 with 16%nat in H3, H by blia.
         simpl in H.
         rewrite H in H3.
         change (104-0) with 104 in H3.
         rewrite map_app.
         array_app_cons_sep.
         cbn [List.length List.map] in *. (*TODO: this can be improved*)
         word_simplify.
         unfold repeat in H3.
         ecancel_assumption. }
         
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H3.
       word_Z_unsigned_in H3.
       pose proof (word.unsigned_range x0).
       assert (List.length (List.skipn x2 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x2 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x2)%nat.
         replace (64 - 4 * Z.of_nat (1 + x2)) with (60 - 4 * Z.of_nat x2) by blia.
         split; auto.
         split; try split; try split; auto.
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x0 - 4).
           blia.
         }
         { pose proof (f_equal word.of_Z H).
           word_Z_unsigned_in H7.
           rewrite H7 in H6.
           change (1 + x2)%nat with (S x2)%nat.
           cbn [List.repeat].
           rewrite repeat_cons.
           array_app_cons_sep.
           rewrite repeat_length, <- List.tl_skipn, H17.
           cbn[List.tl].
           (*Set Ltac Profiling.*)
           repeat word_simplify.
           (*Show Ltac Profile.*)
           repeat word_simplify_in H6.
           word_Z_unsigned_in H6.
           change (66) with (Ox "42") in H6.
           ecancel_assumption.
         }
       }
       eexists; eexists; try blia; destruct H7; auto.
     }
     repeat straightline.

     clear H10.
     pose proof (firstn_skipn 16%nat buf).
     remember (List.skipn 16%nat buf) as buf'.
     pose proof (f_equal (@List.length _) H).
     rewrite H2, app_length, firstn_length in H0.
     assert (List.length buf' = 998)%nat by blia.
     clear H; clear H0; clear Heqbuf'; clear H2.
     do 9 (destruct buf' ; [inversion H3|]).
     inversion H3; clear H3.
     cbn[Array.array] in H1.
     repeat (word_simplify_in H1).
     repeat straightline.
     subst_words.
     clear H7 H6 H5 H4 H3 H2 H1 H.
     repeat word_Z_unsigned_in H8.
     repeat straightline.

     

     
     
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 64 - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ (i < 16)%nat /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"]) * R) M) (fun t m i buf => t = T))) _ _ _ _ _ _ _);
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
     { exists 0%nat.
       split; auto.
       split; try word_Z_unsigned; try split; try split; try blia; auto.
       word_simplify.
       cbn [List.repeat Array.array List.skipn List.map].
       change (Z_of_string "SIG") with 4671827.
       change (Z_of_string "PATH") with 1213481296.
       change (Z_of_string "SREP") with 1346720339.
       change (Z_of_string "CERT") with 1414677827.
       change (Z_of_string "INDX") with 1480871497.
       repeat word_simplify.
       ecancel_assumption. }
     { repeat straightline.
       subst_words.
       word_simplify.
       subst v.
       repeat word_simplify_in H4.
       word_Z_unsigned_in H4.
       assert (List.length (List.skipn x2 buf) <> 0%nat) by (rewrite List.skipn_length; blia).
       destruct (List.skipn x2 buf) eqn:H17; try contradiction.
       array_app_cons_sep.
       repeat straightline.
       subst_words.
       eexists; eexists; split.
       { exists (1 + x2)%nat.
         replace (64 - 4 * Z.of_nat (1 + x2)) with (60 - 4 * Z.of_nat x2) by blia.
         split; auto.
         split; try split; try split; auto.
         { rewrite word.unsigned_sub.
           word_Z_unsigned.
           word_unwrap (word.unsigned x0 - 4).
           blia.
         }
         { rewrite word.unsigned_sub in H5.
           word_Z_unsigned_in H5.
           word_unwrap_in (word.unsigned x - 4) H5.
           blia.
         }
     
     
     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       exists i, V = 64 - 4 * (Z.of_nat i) /\
       V = word.unsigned I /\ (i < 16)%nat /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 40)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (104 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z [5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"]) * R) M
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
       word_Z_unsigned_in H.
       blia. }
     { exists 0%nat.
       split; auto.
       split; try word_Z_unsigned; try split; try split; try blia; auto.
       word_simplify.
       cbn [List.repeat Array.array List.skipn List.map].
       change (Z_of_string "SIG") with 4671827.
       change (Z_of_string "PATH") with 1213481296.
       change (Z_of_string "SREP") with 1346720339.
       change (Z_of_string "CERT") with 1414677827.
       change (Z_of_string "INDX") with 1480871497.
       repeat word_simplify.
       ecancel_assumption. }
     repeat straightline.
     subst_words.
     subst v.
     word_simplify.
     repeat (word_simplify_in H4).
     word_Z_unsigned_in H4.
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
           word_Z_unsigned.
           word_unwrap (word.unsigned x - 4).
           blia.
         }
         { rewrite word.unsigned_sub in H5.
           word_Z_unsigned_in H5.
           word_unwrap_in (word.unsigned x - 4) H5.
           blia.
         }
         pose proof (f_equal word.of_Z H).
         word_Z_unsigned_in H6.
         rewrite H6 in H3.
         change (1 + x1)%nat with (S x1)%nat.
         cbn [List.repeat].
         rewrite repeat_cons.
         array_app_cons_sep.
         rewrite repeat_length, <- List.tl_skipn, H17.
         cbn[List.tl].
         (*Set Ltac Profiling.*)
         repeat word_simplify.
         (*Show Ltac Profile.*)
         repeat word_simplify_in H3.
         word_Z_unsigned_in H3.
         change (66) with (Ox "42") in H3.
         ecancel_assumption.
       - blia.
     }
     clear H4.
     subst br.
     rewrite word.unsigned_sub in H5.
     word_Z_unsigned_in H5.
     word_unwrap_in (word.unsigned x - 4) H5.
     assert (word.unsigned x = 4) by blia.
     pose proof (f_equal word.of_Z H4).
     word_Z_unsigned_in H6.
     rewrite H6 in H3, H.
     repeat word_simplify_in H3.
     word_Z_unsigned_in H.
     assert (x1 = 15)%nat by blia.
     clear H4; clear H6; clear H5.
     rewrite H7 in *; clear H7.
     clear H; clear H1.
     pose proof (f_equal (@List.length _) (firstn_skipn 15 buf)).
     rewrite H2, app_length, firstn_length, H17, List.length_cons, H2 in H.
     assert (List.length l0 = 998)%nat by blia.
     clear H; clear H0; clear H17.
     
     do 9 (destruct l0; [inversion H1|]).
     inversion H1; clear H1.
     cbn[Array.array] in H3.
     repeat (word_simplify_in H3).
     repeat straightline.
     subst_words.
     clear H10 H8 H7 H6 H5 H4 H3 H1 H.
     repeat word_Z_unsigned_in H9.
     repeat straightline.

     remember (map word.of_Z
                   [5; 64; 64; 164; 316; Z_of_string "SIG";
                    Z_of_string "PATH"; Z_of_string "SREP"; 
                    Z_of_string "CERT"; Z_of_string "INDX"]) as buf1.
     

     refine ((TailRecursion.atleastonce ["i"; "buffer"] (fun V T M I BUFFER =>
       exists i, V = 64 - 4 * (Z.of_nat i) /\
       V = word.unsigned I /\ (i < 16)%nat /\ BUFFER = p_addr /\ (array32 (p_addr + (lit 140)) (List.repeat (word.of_Z (Ox"42")) i) * array32 (p_addr + (lit (204 - V))) (List.skipn i buf) * array32 p_addr (List.map word.of_Z ([5; 64; 64; 164; 316; Z_of_string "SIG"; Z_of_string "PATH"; Z_of_string "SREP"; Z_of_string "CERT"; Z_of_string "INDX"] ++ (List.repeat ((Ox"42")) 16) ++ [3; 4; 12; Z_of_string "RADI"; Z_of_string "MIDP"; Z_of_string "ROOT"; Ox"4242"; Ox"42424242"])) * R) M
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
       word_Z_unsigned_in H.
       blia. }
     { exists 0%nat.
       split; auto.
       split; try word_Z_unsigned; try split; try split; try blia; auto.
       word_simplify.
       rewrite map_app, map_app.
       cbn[List.map].
       
       
       cbn [List.map List.repeat List.app Array.array List.skipn].
       
       change (Z_of_string "RADI") with 1229209938.
       change (Z_of_string "MIDP") with 1346652493.
       change (Z_of_string "ROOT") with 1414483794.

       
       
       do 20 word_simplify.
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
         (*Set Ltac Profiling.*)
         repeat word_simplify.
         (*Show Ltac Profile.*)
         repeat word_simplify_in H3.
         change (66) with (Ox "42") in H3.
         ecancel_assumption.
       - blia.
     }
     

     destruct todo.

     
   Qed.


   
   
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
   *)
End WithParameters.

