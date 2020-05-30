Require Import bedrock2.Syntax bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Byte.

Import BinInt String List.ListNotations ZArith.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Require bedrock2Examples.lightbulb_spec.
Local Notation patience := lightbulb_spec.patience.

Require Import coqutil.dlet.

(*

Definition spi_write : function :=
  let b : String.string := "b" in
  let busy : String.string := "busy" in
  let i : String.string := "i" in
  let SPI_WRITE_ADDR := Ox"10024048" in
  ("spi_write", ((b::nil), (busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_WRITE_ADDR);
      if !(busy >> constr:(31)) {
        i = (i^i)
      }
    };
    if !(busy >> constr:(31)) {
      output! MMIOWRITE(SPI_WRITE_ADDR, b);
      busy = (busy ^ busy)
    }
  ))).

Definition spi_read : function :=
  let b : String.string := "b" in
  let busy : String.string := "busy" in
  let i : String.string := "i" in
  let SPI_READ_ADDR := Ox"1002404c" in
  ("spi_read", (nil, (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (constr:(Ox"5a"));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_READ_ADDR);
      if !(busy >> constr:(31)) {
        b = (busy & constr:(Ox"ff"));
        i = (i^i);
        busy = (busy ^ busy)
      }
    }
  ))).

Definition spi_xchg : function :=
  let b : String.string := "b" in
  let busy : String.string := "busy" in
  ("spi_xchg", (b::nil, b::busy::nil, bedrock_func_body:(
    unpack! busy = spi_write(b);
    require !busy;
    unpack! b, busy = spi_read()
  ))).
*)

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.

Import coqutil.Map.Interface.
Import ReversedListNotations.

Import coqutil.Tactics.letexists.
Import TailRecursion.

Require Import bedrock2.Semantics.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Definition mmio_event_abstraction_relation
    (h : lightbulb_spec.OP parameters.word)
    (l : parameters.mem * string * list parameters.word * (parameters.mem * list parameters.word)) :=
    Logic.or
      (exists a v, h = ("st", a, v) /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
      (exists a v, h = ("ld", a, v) /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
  Definition mmio_trace_abstraction_relation := List.Forall2 mmio_event_abstraction_relation.

  Ltac provide_next s :=
    match goal with
    | |- WeakestPrecondition.cmd _ ?c _ _ _ _ =>
      let n := open_constr:(cmd.seq s _) in unify c n
    end.

  Tactic Notation "$" open_constr(s) :=
    provide_next s; repeat straightline.

  Tactic Notation "$" "}" "else" "{" :=
    (* TODO could/should check that we're actually inside an if *)
    match goal with
    | |- WeakestPrecondition.cmd _ ?c _ _ _ _ => unify c cmd.skip
    end; solve [repeat straightline].

  Tactic Notation "$" "}" :=
    match goal with
    | |- WeakestPrecondition.cmd _ ?c _ _ _ _ => unify c cmd.skip
    end.

  (* TODO how can we prevent straightline from deleting them if they're not yet used Lets? *)
  Definition b : String.string := "b".
  Definition busy : String.string := "busy".
  Definition i : String.string := "i".
  Definition SPI_WRITE_ADDR := Ox"10024048".

(*
  Definition call(e: env)(f: string)(t: trace)(m: mem)(args: list word)
             (post: trace -> mem -> list word -> Prop): Prop :=
    exists argnames retnames body,
      map.get e f = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
                forall metrics0,
                  exec e body t m l metrics0
                       (fun t' m' l' _ => exists rets, map.getmany_of_list l' retnames = Some rets /\
                                                       post t' m' rets).
*)

  Definition call(e: env)(f: list string * list string * cmd)(t: trace)(m: mem)(args: list word)
             (post: trace -> mem -> list word -> Prop): Prop :=
    let '(argnames, retnames, body) := f in
    exists l, map.of_list_zip argnames args = Some l /\
              forall metrics0,
                exec e body t m l metrics0
                     (fun t' m' l' _ => exists rets, map.getmany_of_list l' retnames = Some rets /\
                                                     post t' m' rets).

(*
  Record function := {
    fname: string;
    argnames: list string;
    retnames: list string;
    body: cmd;
    pre: trace -> mem -> list word -> Prop;
    post: trace -> mem -> list word -> Prop;
    fcorrect: forall e t m args f,
      map.get e fname = Some f ->
      pre t m args ->
      call e f t m args post;
  }.

  Lemma set: forall e t m metrics l x ev v (post: trace -> mem -> locals -> _ -> Prop),
      WeakestPrecondition.dexpr m l ev v ->
      dlet.dlet (map.put l x v) (fun l0 : locals => forall mc, post t m l0 mc) ->
      exec e (cmd.set x ev) t m l metrics post.
  Admitted.
*)

  Lemma set_cps: forall e t m metrics l0 x ev rest (post: trace -> mem -> locals -> _ -> Prop),
      WeakestPrecondition.expr m l0 ev (fun v =>
         dlet! v := v in
         dlet! l := (map.put l0 x v) in
         exec e rest t m l metrics post) -> (* TODO metrics might change *)
      exec e (cmd.seq (cmd.set x ev) rest) t m l0 metrics post.
  Admitted.

  (* combined with seq, and state updates baked in: *)
  Lemma set: forall e t m metrics l x ev rest v (post: trace -> mem -> locals -> _ -> Prop),
      WeakestPrecondition.dexpr m l ev v ->
      (let l' := (map.put l x v) in exec e rest t m l' metrics post) -> (* TODO metrics might change *)
      exec e (cmd.seq (cmd.set x ev) rest) t m l metrics post.
  Admitted.

  (* Trying to do something like atleastonce:
     inv needs to hold whenever the body is about to be executed.
     Contrary to other loop rules, inv does not need to hold if the loop body is never executed,
     and inv does not need to hold after the last execution of the loop body
     Not useful because needs to prove exec for the rest 2x! *)
  Lemma While: forall (measure : Type) (lt : measure -> measure -> Prop)
                      (inv : measure -> trace -> mem -> locals -> Prop)
                      post t m l mc rest c body (e: env),
      well_founded lt ->
      (exists b : word,
          WeakestPrecondition.dexpr m l c b /\
          (word.unsigned b <> 0 -> exists v0, inv v0 t m l) /\
          (word.unsigned b = 0 -> exec e rest t m l mc post)) ->
      (forall (vi : measure) (ti : trace) (mi : mem) (li : locals) mci,
          inv vi ti mi li ->
          exec e body ti mi li mci (fun t' m' l' mc' =>
             (exists b : word,
                 WeakestPrecondition.dexpr m' l' c b /\
                 (word.unsigned b <> 0 -> exists v', inv v' t' m' l' /\ lt v' vi) /\
                 (word.unsigned b = 0 -> exec e rest t m l mc post)))) ->
      exec e (cmd.seq (cmd.while c body) rest) t m l mc post.
  Abort.

  (* try two invariants: one for done, one for not done
     both user specified?
     --> equivalent to one big invariant which holds before and after the loop, and does
     case distinction on the value of the condition, but the big invariant has the advantage
     that it common invariants can be shared
     the "done" invariant is not the same as Q *)
  Lemma While: forall (measure : Type) (lt : measure -> measure -> Prop)
                      (Inv Q : measure -> trace -> mem -> locals -> Prop)
                      post t1 m1 l1 mc1 b1 rest c body (e: env),
      well_founded lt ->
      WeakestPrecondition.dexpr m1 l1 c b1 ->
      (word.unsigned b1 <> 0 -> exists v, Inv v t1 m1 l1) ->
      (forall v t m l mc b,
          WeakestPrecondition.dexpr m l c b ->
          word.unsigned b <> 0 ->
          Inv v t m l ->
          exec e body t m l mc (fun t' m' l' mc' =>
                                  (* should not be an existential, just an evar ?Q *)
                                  exists v', Q v' t' m' l')) ->
      (forall v t m l,
          Q v t m l ->
          exists b, WeakestPrecondition.dexpr m l c b /\
                    (word.unsigned b <> 0 -> exists v', Inv v t m l /\ lt v' v)) ->
      (forall v t m l mc,
          WeakestPrecondition.dexpr m l c (word.of_Z 0) ->
          t = t1 /\ m = m1 /\ l = l1 \/ Q v t m l -> exec e rest t m l mc post) ->
      exec e (cmd.seq (cmd.while c body) rest) t1 m1 l1 mc1 post.
  Abort.

  (* The invariant needs to hold before we enter the loop and after we exit the loop.
     Often, this will require a case split on whether the loop condition is satisfied,
     which might seem cumbersome at first sight, but it's actually useful, because
     this allows us to control the shape of the symbolic state both before the loop
     body and before code after the loop, and share as many formulas between the
     two as desired. *)
  Lemma While: forall (measure : Type) (lt : measure -> measure -> Prop)
                      (inv : measure -> trace -> mem -> locals -> Prop)
                      (v_init: measure) post metrics t m l rest c body (e: env),
      well_founded lt ->
      inv v_init t m l ->
      (forall (v : measure) (t0 : trace) (m0 : mem) (l0 : locals) mc0,
       inv v t0 m0 l0 ->
       exists b : word,
         WeakestPrecondition.dexpr m0 l0 c b /\
         (word.unsigned b <> 0 -> exec e body t0 m0 l0 mc0 (fun t' m' l' _ =>
            exists v', inv v' t' m' l' /\ lt v' v)) /\
         (word.unsigned b = 0 -> exec e rest t0 m0 l0 mc0 post)) ->
      exec e (cmd.seq (cmd.while c body) rest) t m l metrics post.
  Admitted.

  Lemma If: forall e t m l mc c thn els rest v Q1 Q2 post,
      WeakestPrecondition.dexpr m l c v ->
      (word.unsigned v <> 0 -> exec e thn t m l mc Q1) ->
      (word.unsigned v = 0  -> exec e els t m l mc Q2) ->
      (forall t' m' l' mc', word.unsigned v <> 0 /\ Q1 t' m' l' mc' \/
                            word.unsigned v = 0  /\ Q2 t' m' l' mc' ->
                            exec e rest t' m' l' mc' post) ->
      exec e (cmd.seq (cmd.cond c thn els) rest) t m l mc post.
  Admitted.

  Lemma ExtCall: forall e t1 m1 l1 binds arges args mKeep mGive action rest post mc,
      WeakestPrecondition.dexprs m1 l1 arges args ->
      map.split m1 mKeep mGive ->
      ext_spec t1 mGive action args (fun mReceive rets => exists l : locals,
         map.putmany_of_list_zip binds rets l1 = Some l /\
         (exists m0,
             map.split m0 mKeep mReceive /\
             dlet! t := ((mGive, action, args, (mReceive, rets)) :: t1) in
             exec e rest t m0 l mc post)) ->
      exec e (cmd.seq (cmd.interact binds action arges) rest) t1 m1 l1 mc post.
    Admitted.

  Lemma Skip: forall e t m l mc,
      exec e cmd.skip t m l mc (fun t' m' l' mc' => t' = t /\ m' = m /\ l' = l /\ mc' = mc).
  Proof.
    intros. eapply exec.skip. auto.
  Qed.

  Tactic Notation "$" constr(lhs) "=" constr(rhs) :=
    eapply set_cps with (x := lhs) (ev := rhs); repeat straightline.

  Axiom TODO: False.

  Definition spi_write: (string * {f: list string * list string * cmd &
    forall e t m b,
      word.unsigned b < 2 ^ 8 ->
      call e f t m [b] (fun T M RETS =>
        M = m /\
        exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
          exists err, RETS = [err] /\ Logic.or
       (((word.unsigned err <> 0) /\ lightbulb_spec.spi_write_full _ ^* ioh /\ Z.of_nat (length ioh) = patience))
       (word.unsigned err = 0 /\ lightbulb_spec.spi_write parameters.word (byte.of_Z (word.unsigned b)) ioh))}).

    refine ("spi_write", existT _ (["b"], ["busy"], _) _).

    intros. cbv [call]. straightline. intros.

    $ busy = (-1).
    $ i = patience.

    eapply While with (c := i) (inv := (fun v T M L =>
       (* this part of the loop invariant is needed no matter whether it runs again or we exit: *)
       exists BUSY I,
       L = map.put (map.put (map.put map.empty b b0) busy BUSY) i I /\
       v = word.unsigned I /\
       M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       (* this part of the loop invariant is only needed if we run again: *)
       (word.unsigned I <> 0 ->
          lightbulb_spec.spi_write_full _ ^* th /\
          Z.of_nat (length th) + word.unsigned I = patience)
       )).
    1: exact (Z.lt_wf 0).
    { (* invariant holds initially *)
      eexists. eexists.
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      eexists; split.
      { rewrite app_nil_l; trivial. }
      eexists; split.
      { constructor. }
      split.
      { constructor. }
      subst v0.
      rewrite word.unsigned_of_Z. reflexivity.
    }
    repeat straightline.
    split; repeat straightline.
    { (* loop body *)
      $ i = (expr.op bopname.sub i 1).

      eapply ExtCall with (binds := [busy]) (action := MMIOREAD) (arges := [expr.literal SPI_WRITE_ADDR])
                          (mGive := map.empty).
      {
        cbv [WeakestPrecondition.dexprs  WeakestPrecondition.list_map WeakestPrecondition.list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.literal dlet.dlet].
        reflexivity.
      }
      { eapply Properties.map.split_empty_r. reflexivity. }
      (* TODO how to keep the let but simplify the rest? *)
      change ext_spec with FE310CSemantics.ext_spec.
      cbv beta delta [FE310CSemantics.ext_spec].
      simpl ("MMIOWRITE" =? MMIOREAD)%string. cbv iota.
      simpl ("MMIOREAD" =? MMIOREAD)%string. cbv iota.
      eexists.
      split; [reflexivity|].
      cbv delta [isMMIOAddr].
      rewrite ?word.unsigned_of_Z.
      split. {
        split; [reflexivity|]. split.
        + cbv -[Z.lt Z.gt Z.ge Z.le]; clear.
          Lia.lia.
        + reflexivity.
      }
      repeat straightline.
      eexists. split. {
        eapply Properties.map.split_empty_r. reflexivity.
      }
      straightline.

      eapply If with (c := (expr.op bopname.sru busy 31)); intros; repeat straightline.

      { (* then branch *)
        eapply Skip.
      }
      { (* else branch *)

        $ i = (expr.op bopname.xor i i).
        eapply Skip.
      }

      (* after the if-then-else, still in loop body *)
      eapply exec.skip.

      (* calculated postcondition of loop body implies loop invariant: *)
      cbv beta in *.
      intuition idtac.
      { (* we took the then-branch *)
        subst. eexists. split.
        { eexists. eexists. split. {
            cbv -[v1 v2 v3]. reflexivity. (* takes some time, but whatever *)
          }
          split; [reflexivity|].
          split; [reflexivity|].
          eexists (_ ;++ cons _ nil); split.
          { rewrite <-app_assoc; cbn [app]; f_equal. }
          eexists. split.
          { eapply Forall2_app; eauto.
            constructor; [|constructor].
            right; eauto. }
          split.
          {
          eapply kleene_app; eauto.
          refine (kleene_step _ _ nil _ (kleene_empty _)).
          repeat econstructor.
          repeat match goal with x:=_|-_=>subst x end.
          rewrite Properties.word.unsigned_sru_nowrap in H1 by (rewrite word.unsigned_of_Z; exact eq_refl).
          rewrite word.unsigned_of_Z in H1. unfold not. eapply H1. }
          { rewrite app_length, Znat.Nat2Z.inj_add; cbn [app Datatypes.length].
            intros.
            unshelve erewrite (_ : patience = _); [|symmetry; eassumption|].
            subst v1 v2 v3.
            ring_simplify.
            rewrite <- Z.add_assoc.
            eapply (proj2 (Z.add_cancel_l _ _ _)).
            rewrite word.unsigned_sub.
            rewrite word.unsigned_of_Z. cbv [word.wrap].
            rewrite (Z.mod_small 1). 2: {
              cbv. intuition congruence.
            }
            rewrite Z.mod_small. 1: ring.
            pose proof (Properties.word.unsigned_range x0).
            Lia.blia.
          }
        }
        subst v1 v2 v3.
        rewrite word.unsigned_sub.
        rewrite word.unsigned_of_Z. cbv [word.wrap].
        rewrite (Z.mod_small 1). 2: {
          cbv. intuition congruence.
        }
        pose proof (Properties.word.unsigned_range x0).
        rewrite Z.mod_small; Lia.blia.
      }
      { (* we took the else-branch *)
        subst. eexists. split.
        { eexists. eexists. split. {
            cbv -[v1 v2 v3 word.xor]. reflexivity. (* takes some time, but whatever *)
          }
          split; [reflexivity|].
          split; [reflexivity|].
          eexists (_ ;++ cons _ nil); split.
          { rewrite <-app_assoc; cbn [app]; f_equal. }
          eexists. split.
          { econstructor; try eassumption; right; eauto. }
          intros X.
          rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent in X; contradiction. }
        { rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent.
          subst v1. pose proof (Properties.word.unsigned_range x0). Lia.blia. }
      }
    }

    eapply If with (c := bedrock_expr:(busy >> constr:(31))); intros.
    {
      cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body].
      simpl.
      cbv [WeakestPrecondition.get].
      eexists. simpl. split; [reflexivity|].
      cbv [WeakestPrecondition.literal dlet.dlet]. reflexivity.
    }

    { (* then branch *)
      eapply Skip.
    }
    { (* else branch *)
      eapply ExtCall with (binds := []) (action := MMIOWRITE)
                          (arges := [expr.literal SPI_WRITE_ADDR; expr.var b])
                          (mGive := map.empty).
      {
        cbv [WeakestPrecondition.dexprs  WeakestPrecondition.list_map WeakestPrecondition.list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.literal dlet.dlet
             WeakestPrecondition.get].
        eexists. split.
        { subst l0. reflexivity. }
        reflexivity.
      }
      { eapply Properties.map.split_empty_r. reflexivity. }
      change ext_spec with FE310CSemantics.ext_spec.
      cbv beta delta [FE310CSemantics.ext_spec].
      simpl ("MMIOWRITE" =? MMIOWRITE)%string. cbv iota.
      eexists. eexists.
      split; [reflexivity|].
      cbv delta [isMMIOAddr].
      rewrite ?word.unsigned_of_Z.
      split. {
        split; [reflexivity|]. split.
        + cbv -[Z.lt Z.gt Z.ge Z.le]; clear.
          Lia.lia.
        + reflexivity.
      }
      intros.
      eexists. split; [reflexivity|].
      eexists. split. {
        eapply Properties.map.split_empty_r. reflexivity.
      }
      intros.

      $ busy = (expr.op bopname.xor busy busy).
      eapply Skip.
    }

    eapply exec.skip.
    repeat straightline_cleanup.
    (* prove that computed post implies desired post: *)
    intuition idtac.
    { (* case 1: polling timeout *)
      case TODO. }
    { (* case 2: success *)
      repeat straightline.
      eexists. split. {
        subst l'. unfold busy. reflexivity.
      }
      split; trivial. subst t0 t'.
      eexists (_ ;++ (cons _ nil)). split.
      { rewrite <-app_assoc. cbn [app]. f_equal. }
      eexists. split.
      { eapply List.Forall2_app; eauto.
        constructor.
        { left. eexists _, _; repeat split. }
        constructor.
      }
      eexists; split; trivial.
      right.
      split.
      { f_equal. rewrite Properties.word.unsigned_xor_nowrap; rewrite Z.lxor_nilpotent; reflexivity. }
      cbv [lightbulb_spec.spi_write].
      case TODO.
      (*
      eexists _, _; split; eauto; []; split; eauto.
      eexists (cons _ nil), (cons _ nil); split; cbn [app]; eauto.
      split; repeat econstructor.
      { repeat match goal with x:=_|-_=>subst x end.
        rewrite Properties.word.unsigned_sru_nowrap in H by (rewrite word.unsigned_of_Z; exact eq_refl).
        rewrite word.unsigned_of_Z in H; eapply H. }
      { cbv [lightbulb_spec.spi_write_enqueue one].
        repeat f_equal.
        eapply Properties.word.unsigned_inj.
        clear -p Hb.
        pose proof Properties.word.unsigned_range x.
        change (Semantics.width) with 32 in *.
        change (@Semantics.word (@semantics_parameters p)) with parameters.word in *.
        rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small by Lia.lia.
        rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small; Lia.lia. }
       *)
    }
  Defined.

  Eval unfold spi_write in match spi_write with
                  | (fname, existT _ (argnames, retnames, body) _) => body
                  end.
(*
     = bedrock_func_body:((busy = (constr:(-1)));
                          (i = (constr:(patience)));
                          (while i {
                             (i = (i - constr:(1)));
                             (io! constr:([];+busy) = MMIOREAD (constr:(expr.literal SPI_WRITE_ADDR)));
                             (if !busy >> constr:(31) {
                                (i = (i ^ i));
                                /*skip*/
                              });
                             /*skip*/
                           });
                          (if !busy >> constr:(31) {
                             (io! constr:([]) = MMIOWRITE (constr:(expr.literal SPI_WRITE_ADDR),
                              constr:(expr.var b)));
                             (busy = (busy ^ busy));
                             /*skip*/
                           });
                          /*skip*/)
     : cmd
*)

End WithParameters.
