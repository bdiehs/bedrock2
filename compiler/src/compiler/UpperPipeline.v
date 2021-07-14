Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Import coqutil.Decidable.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.MetricLogging.
Require Import compiler.ExprImp.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.FlatImp.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Import compiler.util.Common.
Require Import compiler.SeparationLogic.
Require Import compiler.Spilling.
Require Import compiler.RegRename.

Section WithWordAndMem.
  Context {width: Z} {word: Interface.word width} {mem : map.map word byte}.

  (* TODO put into common file *)
  Definition trace: Type := list (mem * string * list word * (mem * list word)).
  Definition ExtSpec: Type := trace -> mem -> string -> list word -> (mem -> list word -> Prop) -> Prop.

  Record Lang: Type := {
    Var: Type;
    Cmd: Type;
    Locals : map.map Var word;
    Env : map.map string (list Var * list Var * Cmd);
    Exec: Env -> Cmd -> trace -> mem -> Locals -> MetricLog ->
          (trace -> mem -> Locals -> MetricLog -> Prop) -> Prop
  }.

  Definition phase_correct{L1 L2: Lang}(compile: L1.(Env) -> option L2.(Env)): Prop :=
    forall functions1 functions2 f_entry_name fbody1,
      compile functions1 = Some functions2 ->
      map.get functions1 f_entry_name = Some (nil, nil, fbody1) ->
      exists fbody2,
        map.get functions2 f_entry_name = Some (nil, nil, fbody2) /\
        forall t m mc post, L1.(Exec) functions1 fbody1 t m map.empty mc (fun t' m' l' mc' => post t' m') ->
                            L2.(Exec) functions2 fbody2 t m map.empty mc (fun t' m' l' mc' => post t' m').

  Definition compose_phases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Lemma compose_phases_correct{L1 L2 L3: Lang}
        (compile12: L1.(Env) -> option L2.(Env))
        (compile23: L2.(Env) -> option L3.(Env)):
    phase_correct compile12 -> phase_correct compile23 -> phase_correct (compose_phases compile12 compile23).
  Proof.
    unfold phase_correct, compose_phases. intros C12 C23. intros *. intros ? G1. simp.
    specialize C12 with (1 := E) (2 := G1). simp.
    specialize C23 with (1 := H) (2 := C12p0). simp.
    eexists. split. 1: eassumption.
    intros *. intro Ex1.
    specialize C12p1 with (1 := Ex1).
    specialize C23p1 with (1 := C12p1).
    exact C23p1.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            (ext_spec: ExtSpec)
            (width_cases : width = 32 \/ width = 64)
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Instance W: Words := {| Utility.width_cases := width_cases |}.

    Instance FlattenExpr_parameters: FlattenExpr.parameters := {
      FlattenExpr.W := _;
      FlattenExpr.locals := _;
      FlattenExpr.mem := mem;
      FlattenExpr.ext_spec := ext_spec;
      FlattenExpr.NGstate := N;
    }.

    Context {ext_spec_ok : Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters)}.

    Definition SrcLang := {|
      Var := string;
      Cmd := Syntax.cmd;
      Env := string_keyed_map (list string * list string * Syntax.cmd);
      Exec := Semantics.exec
    |}.

    Definition FlatLangStr := {|
      Var := string;
      Cmd := FlatImp.stmt string;
      Env := string_keyed_map (list string * list string * FlatImp.stmt string);
      Exec := FlatImp.exec
    |}.

    Instance FlatImp_params: FlatImp.parameters Z := {|
      FlatImp.varname_eqb := Z.eqb;
      FlatImp.ext_spec := ext_spec;
    |}.

    Definition FlatLangZ := {|
      Var := Z;
      Cmd := FlatImp.stmt Z;
      Locals := Zlocals;
      Env := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      Exec := FlatImp.exec
    |}.

    Instance mk_FlatImp_string_ext_spec_ok:
      FlatImp.ext_spec.ok string (FlattenExpr.mk_FlatImp_params FlattenExpr_parameters).
    Proof.
      destruct ext_spec_ok.
      constructor.
      all: intros; eauto.
      eapply intersect; eassumption.
    Qed.

    Instance mk_FlatImp_Z_ext_spec_ok:
      FlatImp.ext_spec.ok Z FlatImp_params.
    Proof.
      destruct ext_spec_ok.
      constructor.
      all: intros; eauto.
      eapply intersect; eassumption.
    Qed.

    Lemma flattening_correct: @phase_correct SrcLang FlatLangStr flatten_functions.
    Proof.
      unfold phase_correct. intros.

      pose proof H as GF.
      unfold flatten_functions in GF.
      eapply map.map_all_values_fw in GF. 5: eassumption. 2-4: typeclasses eauto.
      unfold flatten_function in GF. simp.

      eexists. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply @flattenStmt_correct_aux.
        + econstructor; try typeclasses eauto.
        + eassumption.
        + eassumption.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. rewrite map.get_empty in A. discriminate.
        + unfold map.undef_on, map.agree_on. intros. reflexivity.
        + eapply @freshNameGenState_disjoint.
      - simpl. intros. simp. assumption.
    Qed.

    Lemma renaming_correct: @phase_correct FlatLangStr FlatLangZ rename_functions_new.
    Proof.
      unfold phase_correct. intros.

      pose proof H as GR.
      unfold rename_functions_new in GR.
      eapply map.map_all_values_fw in GR. 5: eassumption. 2-4: typeclasses eauto.
      simp. unfold rename_fun_new, rename_binds in GRp0. simp.

      pose proof E as A.
      apply rename_props in A;
        [|eapply map.empty_injective|eapply dom_bound_empty].
      simp.
      eexists. split. 1: eassumption. intros.
      eapply FlatImp.exec.weaken.
      - eapply rename_correct_new with (ext_spec0 := ext_spec).
        2: eassumption.
        { unfold envs_related_new. intros *. intro G.
          eapply map.map_all_values_fw. 5: exact G. 4: eassumption. all: typeclasses eauto. }
        1: eassumption.
        2: {
          eapply Ap2. eapply TestLemmas.extends_refl.
        }
        1: eassumption.
        unfold states_compat. intros *. intro B.
        erewrite map.get_empty in B. discriminate.
      - simpl. intros. simp. assumption.
    Qed.

    Lemma spilling_correct: @phase_correct FlatLangZ FlatLangZ spill_functions.
    Proof.
      unfold phase_correct. intros.

      pose proof H as GL.
      unfold spill_functions in GL.
      eapply map.map_all_values_fw in GL. 5: eassumption. 2-4: typeclasses eauto.
      unfold spill_fun in GL. simp. eapply Bool.andb_true_iff in E.
      destruct E as [_ Fs].
      eapply forallb_vars_stmt_correct in Fs. 2: {
        intros x. split; intros F.
        - rewrite ?Z.ltb_lt in F. exact F.
        - apply Z.ltb_lt. assumption.
      }
      2: {
        intros x. split; intros F.
        - rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
        - apply  Bool.andb_true_iff. rewrite ?Z.ltb_lt. assumption.
      }

      eexists. split. 1: eassumption. intros.

      unfold spill_fbody.
      eapply FlatImp.exec.stackalloc. {
        rewrite Z.mul_comm.
        apply Z_mod_mult.
      }
      intros *. intros Ab Sp.

      assert (BW48: bytes_per_word = 4 \/ bytes_per_word = 8). {
        unfold bytes_per_word.
        (* PARAMRECORDS doesn't work because the record "Words" is not called "parameters" *)
        simpl (@Utility.width _).
        destruct width_cases as [C | C]; rewrite C.
        + change (Memory.bytes_per_word 32) with 4. auto.
        + change (Memory.bytes_per_word 64) with 8. auto.
      }

      eapply FlatImp.exec.weaken.
      - eapply spilling_correct with (ext_spec0 := ext_spec). 2: eassumption.
        { unfold Spilling.envs_related. intros *. intro G.
          pose proof H as GL'.
          unfold spill_functions in GL'.
          eapply map.map_all_values_fw in GL'. 5: exact G. 2-4: typeclasses eauto.
          unfold spill_fun in GL'. simp.
          eapply Bool.andb_true_iff in E. destruct E as (B1 & B3).
          eapply Bool.andb_true_iff in B1. destruct B1 as (B1 & B2).
          eapply List.forallb_to_Forall in B1. 2: {
            intros x F. rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
          }
          eapply List.forallb_to_Forall in B2. 2: {
            intros x F. rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
          }
          eapply forallb_vars_stmt_correct in B3. 2: {
            intros x. split; intros F.
            - rewrite ?Z.ltb_lt in F. exact F.
            - apply Z.ltb_lt. assumption.
          }
          2: {
            intros x. split; intros F.
            - rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
            - apply  Bool.andb_true_iff. rewrite ?Z.ltb_lt. assumption.
          }
          ssplit; try assumption.
          unfold valid_vars_src.
          eapply max_var_sound. exact B3.
        }
        { unfold valid_vars_src.
          eapply max_var_sound. exact Fs. }
        { unfold Spilling.related.
          edestruct hl_mem_to_ll_mem with (mL := mCombined) (mTraded := mStack) (R := emp (map := mem) True)
            as (returned_bytes & L & Q).
          1, 2: eassumption.
          { rewrite sep_emp_r. clear. auto. }
          edestruct (byte_list_to_word_list_array returned_bytes) as (returned_words & LL & QQ). {
            rewrite L. rewrite Z2Nat.id.
            - rewrite Z.mul_comm. apply Z_mod_mult.
            - blia.
          }
          seprewrite_in QQ Q. unfold word_array.
          exists map.empty, map.empty, returned_words.
          ssplit.
          - reflexivity.
          - ecancel_assumption.
          - intros *. rewrite map.get_empty. discriminate.
          - intros *. rewrite map.get_empty. discriminate.
          - unfold sep, map.split. exists map.empty, map.empty.
            rewrite ?map.putmany_empty_r. eauto using map.disjoint_empty_l.
          - unfold sep, map.split, ptsto. eexists map.empty, _. ssplit.
            4: reflexivity.
            + rewrite map.putmany_empty_l. reflexivity.
            + apply map.disjoint_empty_l.
            + exists map.empty, map.empty. unfold tmps. setoid_rewrite map.get_empty.
              rewrite map.putmany_empty_l.
              intuition (eauto using map.disjoint_empty_l || discriminate).
          - intros ? ? ? C. rewrite map.get_empty in C. discriminate C.
          - eapply Nat2Z.inj. rewrite LL. rewrite L. rewrite Z2Nat.id by blia.
            rewrite Z.mul_comm. rewrite Z_div_mult by blia. reflexivity.
        }
      - cbv beta. intros. simp.
        unfold Spilling.related in *. simp.
        match goal with
        | H: (_ * _)%sep m' |- _ => rename H into HM
        end.
        unfold word_array in HM.
        seprewrite_in @cast_word_array_to_bytes HM.
        edestruct ll_mem_to_hl_mem with (mL := m') as (mStack' & HM' & D & Ab'). {
          simpl in *. (* PARAMRECORDS *) ecancel_assumption.
        }
        eexists _, _. ssplit.
        + match goal with
          | |- ?G => let T := type of Ab' in replace G with T; [exact Ab'|clear Ab']
          end.
          f_equal.
          rewrite List.length_flat_map with (n := Z.to_nat bytes_per_word).
          * simpl_addrs. rewrite !Z2Nat.id by blia. simpl in *. (* PARAMRECORDS *) blia.
          * clear. intros. rewrite HList.tuple.length_to_list. reflexivity.
        + rewrite sep_emp_r in HM'. apply proj1 in HM'. subst m'. unfold map.split.
          split. 1: reflexivity. exact D.
        + assumption.
    Qed.

    Definition upper_compiler :=
      compose_phases flatten_functions (compose_phases rename_functions_new spill_functions).

    Lemma upper_compiler_correct: @phase_correct SrcLang FlatLangZ upper_compiler.
    Proof.
      unfold upper_compiler.
      eapply (@compose_phases_correct SrcLang FlatLangStr FlatLangZ). 1: exact flattening_correct.
      eapply (@compose_phases_correct FlatLangStr FlatLangZ FlatLangZ). 1: exact renaming_correct.
      exact spilling_correct.
    Qed.

  End WithMoreParams.
End WithWordAndMem.
