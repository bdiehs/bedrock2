
Require Import bedrock2.Array bedrock2.Scalars bedrock2.SepLogAddrArith.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import bedrock2.Syntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation coqutil.Z.Lia.
Require Import Coq.Strings.Ascii.
Require Import bedrock2.ZnWords.
Require Import bedrock2Examples.memcpy.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Coercion name_of_func (f : func) := fst f.

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
(*
Definition createSignedResponse :=
  let buffer := "buffer" in
  let time := "time" in
  let radius := "radius" in
  let root := "root" in
  ("createSignedResponse", ([buffer; time; radius; root], []: list String.string, bedrock_func_body:(
    store4(buffer + coq:(0), coq:(Ox"3"));
    store4(buffer + coq:(4), coq:(Ox"4"));
    store4(buffer + coq:(8), coq:(Ox"c"));

    store4(buffer + coq:(12), coq:(Z_of_string "RADI"));
    store4(buffer + coq:(16), coq:(Z_of_string "MIDP"));
    store4(buffer + coq:(20), coq:(Z_of_string "ROOT"));
    
    memcpy(buffer + coq:(24), radius, coq:(1));
    memcpy(buffer + coq:(28), radius, coq:(2));
    memcpy(buffer + coq:(36), radius, coq:(16))))).


*)



Definition createTimestampMessage :=
  let buffer := "buffer" in
  let sig := "sig" in
  let time := "time" in
  let radius := "radius" in
  let root := "root" in
  let memcpy := "memcpy" in
  let i := "i" in
  ("createTimestampMessage", ([buffer; sig; time; radius; root], []:list String.string, bedrock_func_body:(
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

    memcpy(buffer + coq:(40), sig, coq:(16));

    store4(buffer + coq:(104), coq:(Ox"3"));
    store4(buffer + coq:(108), coq:(Ox"4"));
    store4(buffer + coq:(112), coq:(Ox"c"));

    store4(buffer + coq:(116), coq:(Z_of_string "RADI"));
    store4(buffer + coq:(120), coq:(Z_of_string "MIDP"));
    store4(buffer + coq:(124), coq:(Z_of_string "ROOT"));
    
    store4(buffer + coq:(128), coq:(Ox"42"));
    store4(buffer + coq:(132), coq:(Ox"42"));
    store4(buffer + coq:(136), coq:(Ox"42"));
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
 
    i = (coq:(32)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(336) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(340), coq:(Ox"42"));
    store4(buffer + coq:(344), coq:(Ox"42"));
    store4(buffer + coq:(348), coq:(Ox"42"));
    store4(buffer + coq:(352), coq:(Ox"42"));
    store4(buffer + coq:(356), coq:(Ox"42"))))).


Require Import bedrock2.ToCString.
Definition prog : string :=
  Eval cbv in c_module [createTimestampMessage].
(*Print prog. *)

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface coqutil.Word.LittleEndian coqutil.Word.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic.
Require Import coqutil.Word.Properties bedrock2.TailRecursion.
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

  Definition stringToWord s : Semantics.word := word.of_Z (Z_of_string s).
  
  Inductive entry :=
  | rec : list (prod string entry) -> entry
  | val : list (Semantics.word) -> entry.

  Fixpoint size (e : entry) : Z :=
    match e with
    | rec l => (Z.of_nat (1 + (2 * List.length l - 1))%nat) + fold_left (fun n e' => n + size (snd e')) l 0
    | val l => Z.of_nat (List.length l)
    end.
  
  Fixpoint compute_offsets' (l : list (prod string entry)) (carry : Z) : list Z :=
    match l with
    | nil => []
    | (_, e) :: l' => (carry + 4 * size e) :: (compute_offsets' l' (carry + 4 * size e))
    end.

  Definition compute_offsets l := removelast (compute_offsets' l 0).
    
  Fixpoint flatten (e : entry) : list (Semantics.word) :=
    match e with
    | rec l => [/_ (Z.of_nat (List.length l))] ++
              List.map word.of_Z (compute_offsets l) ++
              List.map (fun p => stringToWord (fst p)) l ++
              List.concat (List.map (fun p => flatten (snd p)) l)
    | val l => l
    end.

  Definition repeat42 n : list Semantics.word := List.repeat (/_ (Ox"42")) n.

  Definition srep_entry : entry :=
    rec [("RADI", val [/_ (Ox"42")]);
        ("MIDP", val [/_(Ox"42"); /_(Ox"42")]);
        ("ROOT", val (repeat42 16))].
  
  Definition dele_entry : entry :=
    rec [("PUBK", val (repeat42 8));
        ("MINT", val [/_ (Ox"42"); /_ (Ox"42")]);
        ("MAXT", val [/_ (Ox"42"); /_ (Ox"42")])].

  Definition cert_entry : entry :=
    rec [("SIG", val (repeat42 16));
        ("DELE", dele_entry)].

  Definition message_entry sig_entry : entry :=
    rec [("SIG", sig_entry);
        ("PATH", val nil);
        ("SREP", srep_entry);
        ("CERT", cert_entry);
        ("INDX", val [/_ (Ox"42")])].

  Definition message_ok (sig_ok : entry -> Prop) m :=
    exists sig_entry, sig_ok sig_entry /\ m = message_entry sig_entry.


 Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
  
   Ltac subst_words :=
     repeat match goal with x := _ : word.rep |- _ => subst x end.
   
   Notation "l .[[ n |==> xs ]]" := (List.upds l n xs) (left associativity, at level 50).
 
   Ltac word_simplify :=
       match goal with
       | |- context [?a ^+ ?b] => progress (ring_simplify (a ^+ b))
       | |- context [?a ^- ?b] => progress (ring_simplify (a ^- b))
       end.

   Ltac word_Z_unsigned :=
     match goal with
     | H: context [\_ (/_ ?z)] |- _ => rewrite (word.unsigned_of_Z z) in H; change (word.wrap z) with z in H
     | H: context [/_ (\_ ?z)] |- _ => rewrite (word.of_Z_unsigned z) in H
     | |- context [\_ (/_ ?z)] => rewrite (word.unsigned_of_Z z); change (word.wrap z) with z
     | |- context [/_ (\_ ?z)] => rewrite (word.of_Z_unsigned z)
     end.

   Ltac word_Z_unsigned_in H :=
     match type of H with
     | context [\_ (/_ ?z)] => rewrite (word.unsigned_of_Z z) in H; change (word.wrap z) with z in H
     | context [/_ (\_ ?z)] => rewrite (word.of_Z_unsigned z) in H
     end.
   
   Ltac Z_to_nat_div :=
     match goal with
     | |- context [Z.to_nat (?a / 4)] =>
       let r := isZcst a in
       lazymatch r with | true =>
         let x := eval cbv in (Z.to_nat (a/4)) in change (Z.to_nat (a/4)) with x
       end
     | H : context [Z.to_nat (?a / 4)] |- _ =>
       let r := isZcst a in
       lazymatch r with | true =>
         let x := eval cbv in (Z.to_nat (a/4)) in change (Z.to_nat (a/4)) with x in H
       end
     end.
   
   Ltac array_straightline_before :=
     match goal with
     | x : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' ?v _ =>
       match p with
       | context [array32 ?addr ?xs] =>
         eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption |];
         ring_simplify (addr' ^- addr);
         word_Z_unsigned;
         split; [try reflexivity; ZnWords | Z_to_nat_div; split; [repeat rewrite List.upds_length; ZnWords|] ]
       end
     end.

   Ltac upds_simpl_step :=
     match goal with
     | |- context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] =>
       rewrite <- List.upds_app' by (try reflexivity; ZnWords)
     | H : context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] |- _ =>
       rewrite <- List.upds_app' in H by (try reflexivity; ZnWords)
     (*| H : context [ ?l .[[?i |=> ?v]].[[?j |==> ?vs]] ] |- _ =>
       rewrite <-List.upds_cons' in H
     | H : context [ ?l.[[?i |=> ?v]] ] |- _ =>
       rewrite <- List.upds_1 in H*)
     end.
   Ltac upds_simpl := unfold List.upd in *; repeat upds_simpl_step.
   
   Ltac clear_unused :=
     match goal with
     | H0 : (@eq Z _ _) |- _ =>
       match goal with
       | H1 : (sep ?P ?Q) ?m |- context [?m] => clear-H0 H1
       end
     end.
   
   Ltac array_straightline_after :=
     repeat straightline; subst_words; clear_unused; upds_simpl.
   
   Ltac array_straightline := array_straightline_before; array_straightline_after.

   Ltac simpl_list_length_exprs ::= repeat rewrite ?List.length_skipn, ?List.firstn_length, ?List.app_length, ?List.length_cons, ?@List.length_nil, ?List.repeat_length, ?List.upds_length in *.

   Definition repeatLoop end_ :=
     let buffer := "buffer" in
     let i := "i" in
     bedrock_func_body:(while (i) { i = (i - coq:(4));
      store4(buffer + coq:((4 * end_)%Z) - i, coq:(Ox"42"))
    }).
   
   Local Notation tupl := (fun a b c => {|
     PrimitivePair.pair._1 := a;
     PrimitivePair.pair._2 := {|
                           PrimitivePair.pair._1 := b;
                           PrimitivePair.pair._2 :=  {|
                                                     PrimitivePair.pair._1 := c;
                                                     PrimitivePair.pair._2 := tt |} |} |} :  HList.tuple (Semantics.word) (3%nat)).
   Lemma spec_of_repeatLoop :
     forall functions end_ num_iter p_addr sig_addr buf l vs R m t (post : _->_->_->Prop),
       ((array32 p_addr (buf.[[0 |==> vs]])) * R) m ->
       enforce ["i";"buffer";"sig"] (tupl (/_ (4 * num_iter)%Z) p_addr sig_addr) l ->
       0 <= num_iter -> (0 <= end_ < 2 ^ (width - 2)) -> (num_iter <= end_ < Z.of_nat (List.length buf)) -> (end_ = num_iter + Z.of_nat (List.length vs) - 1) ->
       (forall m, ((array32 p_addr (buf.[[0 |==> vs ++ List.repeat (/_ (Ox"42")) (Z.to_nat num_iter)]])) * R) m -> post t m (reconstruct ["i"; "buffer"; "sig"] (tupl (/_ 0) p_addr sig_addr))) ->
         WeakestPrecondition.cmd (WeakestPrecondition.call functions) (repeatLoop end_) t m l post.
   Proof.
     intros.
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ ( HList.polymorphic_list.nil)) ("i"::"buffer"::"sig"::nil)%list%string (fun V R T M I BUFFER SIG => PrimitivePair.pair.mk (exists i, V = 4 * num_iter - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ SIG = sig_addr /\ (array32 p_addr (buf.[[0 |==> vs ++ List.repeat (word.of_Z (Ox"42")) i]]) * R) M) (fun t m i buff sig => t = T /\ i = /_ 0 /\ buff = p_addr /\ sig = sig_addr /\ (array32 p_addr (buf.[[0 |==> vs ++ List.repeat (word.of_Z (Ox"42")) (Z.to_nat num_iter)]]) * R) m))) _ _ _ _ _ _ _);
       cbn [reconstruct map.putmany_of_list HList.tuple.to_list
             HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             
             (* List.repeat *) Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
     { exact H0. }
       { eapply (Z.lt_wf 0). }
       { exists 0%nat.
         split; [auto| split; [ZnWords| split; [auto| split; [auto|] ] ] ] .
         upds_simpl.
         cbn [List.repeat].
         rewrite app_nil_r.
         eassumption. }
       { repeat straightline.
         { subst_words.
           eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption| ZnWords |].  
           replace (\_ (/_ 4)) with 4 by ZnWords. 
           split; [ZnWords| split; [ZnWords|] ].
           repeat straightline.
           eexists; eexists; split.
           { exists (S x3)%nat.
             split; [auto| split; [ZnWords|split; [auto|split; [auto|] ] ] ].
             upds_simpl.
             cbn[List.repeat].
             rewrite List.repeat_cons, List.app_assoc.
             ecancel_assumption. }
           split; [ZnWords|auto]. }

         { split; try split; try split; try split; auto.
           { ZnWords. }
           replace x3 with (Z.to_nat num_iter) in H10 by blia.
           ecancel_assumption. } }
       repeat straightline.
     auto.
   Qed.
    

   Ltac repeat_loop_tac :=
     match goal with
     | |- WeakestPrecondition.cmd _ ?c _ _ ?l0 _ =>
       unfold c, l0
     end;
     match goal with
     | |- WeakestPrecondition.cmd _ (cmd.while (expr.var "i") ?c) _ _ _ _ =>
       unfold c
     end;
     match goal with
     | |- WeakestPrecondition.cmd _ (cmd.while _ (cmd.seq _ (cmd.store access_size.four ((_ + (expr.literal ?e)) - _) _))) _ _ (map.put _ _ (/_ ?n)) _ =>
       let end_ := eval cbn in (e/4) in
       let num_iter := eval cbn in (n/4) in 
       eapply (spec_of_repeatLoop _ (end_) (num_iter));
       [eassumption | repeat straightline | | | | |]; try ZnWords;
       repeat straightline;
       subst_words;
       clear_unused
     end.
   
   Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" :=
     fun functions => forall buf_addr sig_addr buf_data sig_data R m t,
         (array32 buf_addr buf_data * array32 sig_addr sig_data * R) m ->
         List.length buf_data = Z.to_nat 90 ->
         List.length sig_data = Z.to_nat 16 ->
         WeakestPrecondition.call functions "createTimestampMessage" t m [buf_addr; sig_addr]
         (fun t' m' rets => t = t' /\ rets = nil /\
           (array32 buf_addr (flatten (message_entry (val sig_data))) * array32 sig_addr sig_data * R) m').
   
   
   Ltac array_straightline_before ::=
     match goal with
     | x:?p ?m
       |- WeakestPrecondition.store access_size.four ?m (?addr ^+ ?off) ?v _ =>
       match p with
       | context [ array32 addr ?xs ] =>
         eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify ((addr ^+ off) ^- addr); repeat word_Z_unsigned; split;
             [try reflexivity; ZnWords| Z_to_nat_div; split; [ZnWords|] ]
       end
     | x:?p ?m
        |- WeakestPrecondition.store access_size.four ?m ?addr ?v _ =>
       match p with
       | context [ array32 addr ?xs ] =>
         eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption| word_Z_unsigned; blia|];
           ring_simplify (addr ^- addr); repeat word_Z_unsigned; split;
             [ try reflexivity; ZnWords | Z_to_nat_div; split; [ZnWords|] ]
       end
     end.

   Ltac clear_unused ::=
     repeat match goal with
     | H : (?P * ?Q) ?m |- ?G =>
       lazymatch G with
       | context [m] => fail
       | _ =>  clear H
       end
     end.

   Ltac array_ecancel_assumption :=
     match goal with
     | H: context[array32 ?addr (List.upds ?l 0%nat ?xs)] |- _ => 
       rewrite List.upds_0_skipn, (iff1ToEq (array_append _ _ _ _ _)) in H by ZnWords; cbn[List.length] in H; word_Z_unsigned;
       match type of H with
       | context[addr ^+ /_ ?z] => ring_simplify z in H; ecancel_assumption
       end
     end.
   
   Ltac array_straightline_after ::=
     repeat straightline; subst_words; clear_unused; upds_simpl.


   Lemma array_step_ok : (forall buf buf' pref i buf_data v R m (post : _ -> Prop),
                4 * Z.of_nat i < 2 ^ width ->
                i = List.length pref ->
                (i < List.length buf_data)%nat ->
                buf' = buf ^+ /_ ((Z.of_nat i) * 4) ->
                (array32 buf (pref ++ List.skipn i buf_data) * R) m ->
                (forall m, (array32 buf ((pref++[v]) ++ List.skipn (S i) buf_data) * R) m -> post m) ->
                WeakestPrecondition.store access_size.four m buf' v post).
     { intros.
       eapply (array_store_four_of_sep_32bit' buf);
         [reflexivity| ecancel_assumption| word_Z_unsigned; blia |].
       replace (\_ (buf' ^- buf)) with ((Z.of_nat i) *4)%Z by ZnWords.
       subst i.
       word_Z_unsigned.
       split; [ZnWords|].
       rewrite Z.div_mul, Nat2Z.id by blia.
       split; [ZnWords|].
       rewrite List.upd_S_skipn; auto. }
   Qed.  

   Ltac simpl_div4 :=
       match goal with
       | H : context [ (\_ ?e / 4)] |- _ =>
         progress (ring_simplify e in H; word_Z_unsigned; Z_to_nat_div)
       end.

     
     Ltac memcpy_call :=
       straightline_call; [split; [| ecancel_assumption];
         match goal with
         | |- \_ (?a ^- ?b) mod _ = 0 /\ ?P =>
           match a with
           | context[b] => ring_simplify (a ^- b)
           end;
             match P with
             | \_ (?c ^- ?d) mod _ = 0 /\ _ =>
               ring_simplify (c ^- d)
             end
         end;
       repeat word_Z_unsigned;
       repeat split; ZnWords| repeat straightline; clear_unused; word_Z_unsigned; repeat simpl_div4; upds_simpl].
   
   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     repeat array_straightline.
     (* Write ltac to return address given an address expression *)
     cbn[List.app] in H0.
     memcpy_call.
     clear_unused.
     rewrite List.skipn_O in H5.
     subst_words.

     repeat array_straightline.
     repeat_loop_tac.
     repeat array_straightline.
     repeat_loop_tac.
     repeat array_straightline.
     repeat_loop_tac.
     repeat array_straightline.
     
     split; auto; split; auto.

     rewrite List.upds_replace in H0 by ZnWords.
     cbn[List.app] in H0.

     use_sep_assumption.
     cancel.
     cancel_seps_at_indices 0%nat 0%nat.
     { f_equal.
       cbn.
       simpl in H2.
       rewrite H2.
       simpl (Z.of_nat _).
       rewrite List.firstn_all2 by blia.
       simpl repeat.
       rewrite <-?List.app_assoc.
       reflexivity. }
     reflexivity.
   Qed.
   

     
     
     cbn-[Array.array Z.of_nat List.repeat].
     
     replace (Datatypes.length sig_data) with 16%nat.
     rewrite H3.
     ecancel_assumption.
     
     Ltac ecancel_step :=
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify_deltavar LHS y in (* <-- multi-success! *)
      cancel_seps_at_indices i j; [syntactic_exact_deltavar (@eq_refl _ _)|].

      *)
     straightline_call.
     7:{ 

       rewrite (iff1ToEq (sep_comm (array32 _ _) _)).
         ecancel_assumption. }
     { 
       instantiate (1 := 0%nat).
       ring. }
     { match goal with
       | |- 
       instantiate (1 := 10%nat).
       ring. }
     1, 2, 3, 4: ZnWords.
     repeat straightline.
     word_Z_unsigned.
     upds_simpl.
     rewrite List.skipn_O in H6.
     subst_words.
     repeat array_straightline.

     rewrite <-List.upds_app' in H4.
     2:{ simpl_list_length_exprs.
         rewrite min_l.
         { reflexivity. }
         { ZnWords. } }
         simpl.
     upds_simpl.
     eapply (spec_of_repeatLoop _ 50 16).
     { eassumption.
      
     
     
     match goal with
  | x:?p ?m
    |- WeakestPrecondition.store access_size.four ?m (?addr ^+ ?off) ?v _ =>
        match p with
        | context [ array32 addr ?xs ] =>
            eapply array_store_four_of_sep_32bit';
             [ reflexivity | ecancel_assumption | word_Z_unsigned; blia |  ];
             ring_simplify addr ^+ off ^- addr; repeat word_Z_unsigned; split;
             [ try reflexivity; ZnWords | Z_to_nat_div; split; [ ZnWords |  ] ]
        end
  | x:?p ?m
    |- WeakestPrecondition.store access_size.four ?m ?addr ?v _ =>
        match p with
        | context [ array32 addr ?xs ] =>
            eapply array_store_four_of_sep_32bit';
             [ reflexivity | ecancel_assumption | word_Z_unsigned; blia |  ];
             ring_simplify addr ^- addr; repeat word_Z_unsigned; split;
             [ try reflexivity; ZnWords | Z_to_nat_div; split; [ ZnWords |  ] ]
        end
  end
     
     array_straightline.
     
     
     
       instantiate (1 := firstn ((buf ^+ 40 ^- buf) / 4) buf_data.[[updated]])
       use_sep_assumption.
       cancel.
       Ltac pick_nat n :=
       multimatch n with
       | S ?m => idtac m; constr:(m)
       | S ?m => idtac m; pick_nat m
       end.
       
       Ltac find_context_in_list xs y :=
         multimatch xs with
         | ?x :: _ => match x with
                    | context [y] => constr:(0%nat)
                    | _ => fail
                    end
         | _ :: ?xs => let i := find_context_in_list xs y in
                     constr:(S i)
         end.

       let LHS := lazymatch goal with
                  | |- iff1 (seps ?LHS) _ => LHS
                  end in
       let RHS := lazymatch goal with
                  | |- iff1 _ (seps ?RHS) => RHS
                  end in
       let iy := index_and_element_of LHS in
       let i := match iy with | (?i, _) => i end in
       let addr := match iy with | (_, array32 ?addr _) => addr end in 
       let j := find_context_in_list RHS buf in idtac j.
       cancel_seps_at_indices 0%nat 1%nat.
       let idk := find_context_in_list RHS buf in
       idtac idk.
       
       let LHS := lazymatch goal with
             | |- iff1 (seps ?LHS) _ => LHS
             end in
       let iy := index_and_element_of LHS in idtac iy.
       let idk := find_context_in_list 
                      
       let r := (pick_nat S%nat) in idtac r.
     
       
       match goal with
       | H: ?p ?m |- ?q ?m =>
         match p with
         | context [array32 ]

       is_var buf.
       is_const List.length.
       is_var l.
       assert (i : Semantics.word) by admit.
       replace (/_40) with (/_40 ^+ i) by admit.
       ring_simplify (buf ^+ (/_ 40 ^+ i)).

       (* if separation logic preds in hypotheses are fully merged then addresses are just variables *)
       
       
       use_sep_assumption.
       cancel.
       cancel_seps_at_indices 1%nat 0%nat.
       1: reflexivity.
       admit. }

     4:{
       repeat straightline.
       
       Search sep List.skipn List.firstn.
     
     rewrite List.upds_0_skipn in H0 by ZnWords.
     cbn[List.length] in H0.
     rewrite (iff1ToEq (array_append _ _ _ _ _)) in H0 by ZnWords; cbn[List.length] in H0; word_Z_unsigned.
     ring_simplify (4 * Z.of_nat 10)%Z in H0.
     straightline_call. 4:{
     4: ecancel_assumption.
     1, 2, 3: word_Z_unsigned; ZnWords.
     repeat straightline.
     repeat clear_unused.
     word_Z_unsigned_in H6.
     rewrite List.firstn_all2 in H6 by blia.
     change (/_ 40) with (/_ (4 * 10)) in H6.

     assert ((array32 buf (buf_data.[[0|==> [/_ 5; /_ 64; /_ 64; /_ 164; /_ 316; /_ 4671827; /_ 1213481296; /_ 1346720339; /_ 1414677827; /_ 1480871497] ++ sig_data]]) * array32 sig sig_data * R) a0).
     { rewrite List.upds_0_skipn by ZnWords.
       rewrite List.app_length.
       cbn[List.length].
       rewrite (iff1ToEq (array_append _ _ _ _ _)), List.app_length by ZnWords.
       cbn[List.length].
       word_Z_unsigned.
       unfold List.upds in H6.
       rewrite List.firstn_O, Nat.sub_0_r, Nat.add_0_r, List.skipn_length, List.firstn_all2, List.skipn_skipn, List.app_nil_l in H6 by blia.
       rewrite (iff1ToEq (array_append _ _ _ _ _)) in H6.
       word_Z_unsigned_in H6.
       ring_simplify (buf ^+ /_ (4 * 10) ^+ /_ (4 * Z.of_nat (Datatypes.length sig_data))) in H6.
       rewrite Nat2Z.inj_add.
       ring_simplify (buf ^+ /_ (4 * (Z.of_nat 10 + Z.of_nat (Datatypes.length sig_data)))).
       rewrite Nat.add_comm.
       rewrite (iff1ToEq (array_append _ _ _ _ _)).
       word_Z_unsigned.
       cbn[List.length].
       change (Z.of_nat 10) with 10.
       ring_simplify (buf ^+ /_ (4 * 10)).
       ring_simplify (buf ^+ (/_ 4 ^* /_ 10)) in H6.
       ecancel_assumption. }
     clear H6.

     subst_words.
     repeat array_straightline.
     rewrite <-List.upds_app2 in H4.
     2:{  simpl_list_length_exprs. setoid_rewrite List.length_nil. blia. }
     
     eapply (spec_of_repeatLoop _ 50 16).
     1:eassumption.
     { repeat straightline. }
     
     
     match goal with
     | x:?p ?m
       |- WeakestPrecondition.store access_size.four ?m (?addr ^+ ?off) ?v _ =>
       match p with
       | context [ array32 addr ?xs ] =>
         eapply array_store_four_of_sep_32bit';
           [ reflexivity | ecancel_assumption | word_Z_unsigned; try blia |  ];
           ring_simplify (addr ^+ off ^- addr); repeat word_Z_unsigned; split;
             [ try reflexivity; ZnWords | Z_to_nat_div; split; [ ZnWords |  ] ]
       end
     end.
     
     array_straightline_before.
     
     repeat array_straightline.
       

     change buf_data with ([] ++ (List.skipn 0 buf_data)) in H0.

     Local Ltac idk :=
       eapply array_step_ok; [| | | | ecancel_assumption|]; [ZnWords|reflexivity | blia| try reflexivity; ZnWords|];
       repeat straightline;
       repeat clear_unused;
       subst_words.
     repeat idk.

     
     cbn[List.app] in H0.
     
     eapply array_step; [| | | | ecancel_assumption|];
       [ZnWords|reflexivity |blia |reflexivity |].
     4:{ reflexivity.
     1: ZnWords.
     1: reflexivity.
     1: blia.
     1:{ reflexivity. ZnWords_pre. reflexivity. ZnWords.
     idk.
     idk.
     idk.
     
     
     { ZnWords.
       
       word_Z_unsigned.
       rewrite (word.unsigned_of_Z (4 * Z.of_nat i)).
       unfold word.wrap.
       rewrite (Z.mod_small (4 * Z.of_nat i)).
       replace (word.wrap (4 * Z.of_nat i)) with (4 * Z.of_nat i).
       
         ring_simplify ( (buf ^+ /_ (4 * (Z.of_nat i))) ^- buf0); repeat word_Z_unsigned.
           split; [try reflexivity; ZnWords|Z_to_nat_div; split; [ZnWords|] ].
       
       

     Ltac idk :=
       match goal with
       | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
         match P with
         | context [array32 ?addr ?xs] =>
           eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
           split; [try reflexivity; ZnWords|Z_to_nat_div; split; [ZnWords|] ]
         end
       end; rewrite upd_S_skipn; [|reflexivity|blia]; repeat straightline; subst_words; repeat clear_unused.
     Set Ltac Profiling.
     cbn[List.app List.skipn] in H0.
     repeat array_straightline.
     Show Ltac Profile.
     idk.
     
     Ltac idk :=
       match goal with
       | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
         match P with
         | context [array32 ?addr ?xs] =>
           eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
           split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
         end
       end; repeat straightline; subst_words; repeat clear_unused;
       match goal with
       | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
         match P with
         | context [array32 ?addr ?xs] =>
           try (rewrite List.upd_0_skipn in H by ZnWords);
           try (rewrite List.upd_S_skipn in H; [|reflexivity| ZnWords])
         end
       end.
     Set Ltac Profiling.
     repeat array_straightline.
     Show Ltac Profile.

     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
             split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
       end
     end.
     repeat straightline.
     subst_words.
     repeat clear_unused.
     rewrite List.upd_0_skipn in H4 by ZnWords.

     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
             split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
       end
     end.
     repeat straightline.
     subst_words.
     repeat clear_unused.
     rewrite List.upd_S_skipn in H0; [|reflexivity| ZnWords].

     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
             split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
       end
     end.
     repeat straightline.
     subst_words.
     repeat clear_unused.
     rewrite List.upd_S_skipn in H4; [|reflexivity| ZnWords].
     
     Ltac idk :=
       match goal with
       | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
         match P with
         | context [array32 ?addr ?xs] =>
           eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
           split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
         end
       end; repeat straightline; subst_words; repeat clear_unused;
       match goal with
       | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
         match P with
         | context [array32 ?addr ?xs] =>
           tryif rewrite List.upd_0_skipn in H then idtac else
             rewrite List.upd_S_skipn in H; [|reflexivity| ZnWords]
         end
       end.
     idk.
       
       
     
     
     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 ?addr ?xs] =>
         eapply (array_store_four_of_sep_32bit' addr);
           [reflexivity| ecancel_assumption| word_Z_unsigned; blia |];
           ring_simplify (addr' ^- addr); repeat word_Z_unsigned;
             split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ]
       end
     end.
     repeat straightline.
     subst_words.

     eapply (array_store_four_of_sep_32bit' buf);
       [reflexivity| ecancel_assumption| word_Z_unsigned; blia|].
     ring_simplify  (buf ^+ /_ 4 ^- buf). repeat word_Z_unsigned.
     split; [ZnWords|Z_to_nat_div; split; [|] ].
     { rewrite List.upd_length.
       blia. }
     repeat straightline.
     subst_words.
     repeat clear_unused.
     
     
     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 ?addr ?xs] =>
         tryif rewrite List.upd_0_skipn in H by ZnWords then idtac else rewrite List.upd_S_skipn in H by ZnWords
       end
     end.

     eapply (array_store_four_of_sep_32bit' buf);
       [reflexivity| | |].
     
     
     rewrite (iff1ToEq (array_append' _ _ _ _ _)) in H4.
     cbn[List.length] in H4.
     match goal with
     | H : ?P ?m |- WeakestPrecondition.store access_size.four ?m ?addr' _ _ =>
       match P with
       | context [array32 (?addr ^+ ?off) ?xs] => ring_simplify (addr ^+ off) in H
       end
     end.
     
     
     
     change buf_data with (nil ++ (List.skipn 0 buf_data)) in H0.
     
     subst_words.
     eapply (array_store_four_of_sep_32bit' buf);
       [reflexivity| ecancel_assumption| word_Z_unsigned; blia |].
     ring_simplify (buf ^- buf); repeat word_Z_unsigned.
     split. { ZnWords_pre.
     split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ].
     repeat straightline.
     repeat clear_unused.
     
     rewrite upd_S_skipn in H4; [|reflexivity|ZnWords].

     array_straightline_before.
     repeat straightline.
     
     unfold List.upd in H4.
     rewrite List.upds_skipn in H4 by ZnWords.
     cbn[List.app List.length] in H4.

     subst_words.
     eapply (array_store_four_of_sep_32bit' buf);
       [reflexivity| ecancel_assumption| word_Z_unsigned; blia |].
     ring_simplify (buf ^+ /_ 4 ^- buf); repeat word_Z_unsigned.
     split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ].
     repeat straightline.
     repeat clear_unused.
     change (/_ 5::List.skipn 1 buf_data) with ([/_ 5]++List.skipn 1 buf_data) in H5.
     rewrite upd_S_skipn in H5; [|reflexivity|ZnWords].

     
     
     subst_words.
     eapply (array_store_four_of_sep_32bit' buf);
       [reflexivity| ecancel_assumption| word_Z_unsigned; blia |].
     ring_simplify (buf ^+ /_ 8 ^- buf); repeat word_Z_unsigned.
     split; [ZnWords|Z_to_nat_div; split; [ZnWords|] ].
     repeat straightline.
     repeat clear_unused.
     rewrite upd_S_skipn in H0; [|reflexivity|ZnWords].
     

     unfold List.upd in H5.
     rewrite List.upds_skipn in H5 by ZnWords.

     
     repeat array_straightline.

     cbn[List.app List.length] in H4.
     
     (*
forall functions end_ num_iter p_addr buf l vs R m t (post : _->_->_->Prop),
       ((array32 p_addr (buf.[[0 |==> vs]])) * R) m ->
       enforce ["i";"buffer"] (tupl (/_ (4 * num_iter)%Z) p_addr) l ->
       0 <= num_iter -> (0 <= end_ < 2 ^ (width - 2)) -> (num_iter <= end_ < Z.of_nat (List.length buf)) -> (end_ = num_iter + Z.of_nat (List.length vs) - 1) ->
       (forall m, ((array32 p_addr (buf.[[0 |==> vs ++ List.repeat (/_ (Ox"42")) (Z.to_nat num_iter)]])) * R) m -> post t m (reconstruct ["i"; "buffer"] (tupl (/_ 0) p_addr))) ->
         WeakestPrecondition.cmd (WeakestPrecondition.call functions) (repeatLoop end_) t m l post.
*)

     assert (forall buf buf_data xs R t m post,
                (array32 buf (List.upds buf_data 0%nat xs) * R) m ->
                
                WeakestPrecondition.call functions "memcpy" t m args post).

     straightline_call; repeat word_Z_unsigned.
     4:{
     
     
     straightline_call; repeat word_Z_unsigned
       ;[| | | array_ecancel_assumption|].
     1, 2, 3: ZnWords.
     repeat straightline.
     
     
     repeat array_straightline.
     
     4:{ ecancel_assumption.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     split; [auto |split; [auto|] ].

     (* (List.length l = length buf) -> buf. [[0|==>l]] = l *)
     rewrite List.upds_replace in H by ZnWords.
     exact 
     
   Qed.

















  
  

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
    store4(buffer + coq:(132), coq:(Ox"42"));
    store4(buffer + coq:(136), coq:(Ox"42"));
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
 
    i = (coq:(32)); while (i) { i = (i - coq:(4));
      store4(buffer + coq:(336) - i, coq:(Ox"42"))
    };

    store4(buffer + coq:(340), coq:(Ox"42"));
    store4(buffer + coq:(344), coq:(Ox"42"));
    store4(buffer + coq:(348), coq:(Ox"42"));
    store4(buffer + coq:(352), coq:(Ox"42"));
    store4(buffer + coq:(356), coq:(Ox"42"))))).
    
Require Import bedrock2.ToCString.
   Definition allProgsAsCString : string :=
     Eval cbv in c_module [createTimestampMessage].
   Print allProgsAsCString.

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
  
  Definition stringToWord (s : string) := word.of_Z (Z_of_string s).

  Inductive entry :=
  | rec : list (prod string entry) -> entry
  | val : list (Semantics.word) -> entry.

  Fixpoint size (e : entry) : Z :=
    match e with
    | rec l => (Z.of_nat (1 + (2 * List.length l - 1))%nat) + fold_left (fun n e' => n + size (snd e')) l 0
    | val l => Z.of_nat (List.length l)
    end.
  
  Fixpoint compute_offsets' (l : list (prod string entry)) (carry : Z) : list Z :=
    match l with
    | nil => []
    | (_, e) :: l' => (carry + 4 * size e) :: (compute_offsets' l' (carry + 4 * size e))
    end.

  Definition compute_offsets l := removelast (compute_offsets' l 0).
    
  Fixpoint flatten (e : entry) : list (Semantics.word) :=
    match e with
    | rec l => [/_ (Z.of_nat (List.length l))] ++
              List.map word.of_Z (compute_offsets l) ++
              List.map (fun p => stringToWord (fst p)) l ++
              List.concat (List.map (fun p => flatten (snd p)) l)
    | val l => l
    end.

  Definition repeat42 n := List.repeat (/_ (Ox"42")) n.

  Definition srep_entry : entry :=
    rec [("RADI", val [/_ (Ox"42")]);
        ("MIDP", val [/_(Ox"42"); /_(Ox"42")]);
        ("ROOT", val (repeat42 16))].
  
  Definition dele_entry : entry :=
    rec [("PUBK", val (repeat42 8));
        ("MINT", val [/_ (Ox"42"); /_ (Ox"42")]);
        ("MAXT", val [/_ (Ox"42"); /_ (Ox"42")])].

  Definition cert_entry : entry :=
    rec [("SIG", val (repeat42 16));
        ("DELE", dele_entry)].

  Definition message_entry : entry :=
    rec [("SIG", val (repeat42 16));
        ("PATH", val nil);
        ("SREP", srep_entry);
        ("CERT", cert_entry);
        ("INDX", val [/_ (Ox"42")])].

  (*
  Definition message_entry : entry :=
    rec [("SIG", val (repeat42 16));
        ("PATH", val nil);
        ("SREP", rec [("RADI", val [/_ (Ox"42")]);
                     ("MIDP", val [/_(Ox"42"); /_(Ox"42")]);
                     ("ROOT", val (repeat42 16))]);
        ("CERT", rec [("SIG", val (repeat42 16));
                     ("DELE", rec [("PUBK", val (repeat42 8));
                                  ("MINT", val [/_ (Ox"42"); /_ (Ox"42")]);
                                  ("MAXT", val [/_ (Ox"42"); /_ (Ox"42")])])]);
        ("INDX", val (repeat42 64))].
  *)

   Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
  
   Ltac subst_words :=
     repeat match goal with x := _ : word.rep |- _ => subst x end.
   
   Notation "a |-> v" := (scalar32 a (/_ v)) (at level 30).
   Notation "l .[[ n |=> v ]]" := (List.upd l n v) (left associativity, at level 50).
   Notation "l .[[ n |==> xs ]]" := (List.upds l n xs) (left associativity, at level 50).
 
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
   
   Ltac Z_to_nat_div :=
     match goal with
     | |- context [Z.to_nat (?a / 4)] =>
       let r := isZcst a in
       lazymatch r with | true =>
         let x := eval cbv in (Z.to_nat (a/4)) in change (Z.to_nat (a/4)) with x
       end
     end.
   
   Ltac array_straightline_before :=
     match goal with
     | x : ?p ?m |- @WeakestPrecondition.store _ Syntax.access_size.four ?m ?addr' ?v _ =>
       match p with
       | context [array32 ?addr ?xs] =>
         eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption | ZnWords|];
         ring_simplify (addr' ^- addr);
         repeat word_Z_unsigned;
         split; [try reflexivity; ZnWords | Z_to_nat_div; split; [repeat rewrite List.upds_length; ZnWords|] ]
       end
     end.

   Ltac upds_simpl_step :=
     match goal with
     | |- context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] =>
       rewrite <- List.upds_app2 by (try reflexivity; ZnWords)
     | H : context [ ?l.[[?i |==> ?vs]].[[?j |==> ?vs']] ] |- _ =>
       rewrite <- List.upds_app2 in H by (try reflexivity; ZnWords)
     (*| H : context [ ?l .[[?i |=> ?v]].[[?j |==> ?vs]] ] |- _ =>
       rewrite <-List.upds_cons' in H
     | H : context [ ?l.[[?i |=> ?v]] ] |- _ =>
       rewrite <- List.upds_1 in H*)
     end.
   Ltac upds_simpl := unfold List.upd in *; repeat upds_simpl_step.
   
   Ltac clear_unused :=
     match goal with
     | H0 : (@eq Z _ _) |- _ =>
       match goal with
       | H1 : (sep ?P ?Q) ?m |- context [?m] => clear-H0 H1
       end
     end.
   
   Ltac array_straightline_after :=
     repeat straightline; subst_words; clear_unused; upds_simpl.
   
   Ltac array_straightline := array_straightline_before; array_straightline_after.

   Ltac simpl_list_length_exprs ::= rewrite ?List.length_skipn, ?List.firstn_length, ?List.app_length, ?List.length_cons, ?List.length_nil, ?List.repeat_length, ?List.upds_length in *.

   Definition repeatLoop end_ :=
     let buffer := "buffer" in
     let i := "i" in
     bedrock_func_body:(while (i) { i = (i - coq:(4));
      store4(buffer + coq:((4 * end_)%Z) - i, coq:(Ox"42"))
    }).

   Local Notation tupl := (fun a b =>{|
     PrimitivePair.pair._1 := a;
     PrimitivePair.pair._2 := {|
                           PrimitivePair.pair._1 := b;
                           PrimitivePair.pair._2 := tt |} |} :  HList.tuple (Semantics.word) (2%nat)).
   Lemma spec_of_repeatLoop :
     forall functions end_ num_iter p_addr buf l vs R m t (post : _->_->_->Prop),
       ((array32 p_addr (buf.[[0 |==> vs]])) * R) m ->
       enforce ["i";"buffer"] (tupl (/_ (4 * num_iter)%Z) p_addr) l ->
       0 <= num_iter -> (0 <= end_ < 2 ^ (width - 2)) -> (num_iter <= end_ < Z.of_nat (List.length buf)) -> (end_ = num_iter + Z.of_nat (List.length vs) - 1) ->
       (forall m, ((array32 p_addr (buf.[[0 |==> vs ++ List.repeat (/_ (Ox"42")) (Z.to_nat num_iter)]])) * R) m -> post t m (reconstruct ["i"; "buffer"] (tupl (/_ 0) p_addr))) ->
         WeakestPrecondition.cmd (WeakestPrecondition.call functions) (repeatLoop end_) t m l post.
   Proof.
     intros.
     refine ((TailRecursion.tailrec (HList.polymorphic_list.cons _ HList.polymorphic_list.nil) ("i"::"buffer"::nil)%list%string (fun V R T M I BUFFER => PrimitivePair.pair.mk (exists i, V = 4 * num_iter - 4 * (Z.of_nat i) /\ V = word.unsigned I /\ BUFFER = p_addr /\ (array32 p_addr (buf.[[0 |==> vs ++ List.repeat (word.of_Z (Ox"42")) i]]) * R) M) (fun t m i buff => t = T /\ i = /_ 0 /\ buff = p_addr /\ (array32 p_addr (buf.[[0 |==> vs ++ List.repeat (word.of_Z (Ox"42")) (Z.to_nat num_iter)]]) * R) m))) _ _ _ _ _ _ _);
       cbn [reconstruct map.putmany_of_list HList.tuple.to_list
             HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             
             (* List.repeat *) Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
     { exact H0. }
       { eapply (Z.lt_wf 0). }
       { exists 0%nat.
         split; [auto| split; [ZnWords| split; [auto|] ] ] .
         upds_simpl.
         cbn [List.repeat].
         rewrite app_nil_r.
         eassumption. }
       { repeat straightline.
         { subst_words.
           eapply array_store_four_of_sep_32bit'; [reflexivity| ecancel_assumption| ZnWords |].
           replace (\_ (/_ 4)) with 4 by ZnWords. 
           split; [ZnWords| split; [ZnWords|] ].
           repeat straightline.
           eexists; eexists; split.
           { exists (S x2)%nat.
             split; [auto| split; [ZnWords|split; [auto|] ] ].
             upds_simpl.
             cbn[List.repeat].
             rewrite List.repeat_cons, List.app_assoc.
             ecancel_assumption. }
           split; [ZnWords|auto]. }

         { split; try split; try split; auto.
           { ZnWords. }
           replace x2 with (Z.to_nat num_iter) in H9 by blia.
           ecancel_assumption. } }
       repeat straightline.
     auto.
   Qed.


   Ltac repeat_loop_tac :=
     match goal with
     | |- WeakestPrecondition.cmd _ ?c _ _ ?l0 _ =>
       unfold c, l0
     end;
     match goal with
     | |- WeakestPrecondition.cmd _ (cmd.while (expr.var "i") ?c) _ _ _ _ =>
       unfold c
     end;
     match goal with
     | |- WeakestPrecondition.cmd _ (cmd.while _ (cmd.seq _ (cmd.store access_size.four ((_ + (expr.literal ?e)) - _) _))) _ _ (map.put _ _ (/_ ?n)) _ =>
       let end_ := eval cbn in (e/4) in
       let num_iter := eval cbn in (n/4) in 
       eapply (spec_of_repeatLoop _ (end_) (num_iter));
       [eassumption | repeat straightline | | | | |]; try ZnWords;
       repeat straightline;
       subst_words;
       clear_unused
     end.
   
   
   Instance spec_of_createTimestampMessage : spec_of "createTimestampMessage" :=
     fun functions => forall p_addr buf R m t,
         ((array32 p_addr buf) * R) m ->
         Z.of_nat (List.length buf) = 90 ->
         WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr]
         (fun t' m' rets => t = t' /\ rets = nil /\ ((array32 p_addr (flatten message_entry)) * R) m').
   

   Lemma createTimestampMessage_ok : program_logic_goal_for_function! createTimestampMessage.
   Proof.
     repeat straightline.
     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     repeat_loop_tac.

     repeat array_straightline.
     split; [auto |split; [auto|] ].

     rewrite List.upds_replace in H by ZnWords.
     exact H.
     
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

