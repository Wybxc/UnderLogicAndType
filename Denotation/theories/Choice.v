(** Choice preserves right-branch under coverage and requires totality of
    both branches.  Irrelevant store entries need not be closed. *)
From Denotation Require Import Notation TypeDenote TypeEquivCore TypeEquiv BaseCoverage.
From CoreLang Require Import Choice InstantiationProps StrongNormalization.

Lemma fv_choose_tm left right :
  lc_tm left -> lc_tm right ->
  fv_tm (choose_tm left right) = fv_tm left ∪ fv_tm right.
Proof.
  intros Hl Hr. unfold choose_tm. rewrite !tm_shift_lc_id by assumption.
  cbn [fv_tm fv_value]. set_solver.
Qed.

Lemma instantiate_lift_restrict_atoms σ e X :
  fv_tm e ⊆ X ->
  lstore_instantiate_tm (lstore_lift_free (store_restrict σ X)) e =
    lstore_instantiate_tm (lstore_lift_free σ) e.
Proof.
  intros Hfv. unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite !lstore_free_part_lift_free.
  rewrite !lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  apply lstore_instantiate_tm_split_restrict_fv. exact Hfv.
Qed.

Lemma instantiate_lift_as_msubst σ e :
  closed_env σ ->
  lstore_instantiate_tm (lstore_lift_free σ) e = msubst σ e.
Proof.
  intros Hσ. unfold lstore_instantiate_tm.
  rewrite lstore_instantiate_tm_at_lc_lstore.
  - rewrite lstore_free_part_lift_free. apply subst_map_tm_eq_msubst.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact Hσ.
Qed.

Lemma instantiate_lift_lc_on σ e X :
  lc_tm e -> fv_tm e ⊆ X -> store_closed (store_restrict σ X) ->
  lc_tm (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros He Hfv [Hclosed Hlc].
  rewrite <- (instantiate_lift_restrict_atoms σ e X Hfv).
  rewrite instantiate_lift_as_msubst by exact Hclosed. apply msubst_lc; assumption.
Qed.

Lemma instantiate_lift_choose_tm σ left right :
  lc_tm left -> lc_tm right ->
  store_closed (store_restrict σ (fv_tm left ∪ fv_tm right)) ->
  lstore_instantiate_tm (lstore_lift_free σ) (choose_tm left right) =
    choose_tm (lstore_instantiate_tm (lstore_lift_free σ) left)
      (lstore_instantiate_tm (lstore_lift_free σ) right).
Proof.
  intros Hl Hr Hclosed.
  set (X := fv_tm left ∪ fv_tm right).
  rewrite <- (instantiate_lift_restrict_atoms σ (choose_tm left right) X)
    by (rewrite fv_choose_tm by assumption; reflexivity).
  rewrite <- (instantiate_lift_restrict_atoms σ left X) by (unfold X; set_solver).
  rewrite <- (instantiate_lift_restrict_atoms σ right X) by (unfold X; set_solver).
  rewrite !instantiate_lift_as_msubst by exact (proj1 Hclosed).
  apply msubst_choose_tm; [exact (proj2 Hclosed)|exact Hl|exact Hr].
Qed.

Lemma choose_tm_store_results σ left right v :
  lc_tm left -> lc_tm right ->
  store_closed (store_restrict σ (fv_tm left ∪ fv_tm right)) ->
  (tm_eval_in_store σ (choose_tm left right) v <->
    tm_eval_in_store σ left v \/ tm_eval_in_store σ right v).
Proof.
  intros Hl Hr Hclosed. unfold tm_eval_in_store, expr_eval_in_store.
  rewrite instantiate_lift_choose_tm by assumption.
  apply choose_tm_results.
  - eapply instantiate_lift_lc_on with (X := fv_tm left ∪ fv_tm right);
      [exact Hl|clear; set_solver|exact Hclosed].
  - eapply instantiate_lift_lc_on with (X := fv_tm left ∪ fv_tm right);
      [exact Hr|clear; set_solver|exact Hclosed].
Qed.

Lemma choose_tm_store_total σ left right :
  lc_tm left -> lc_tm right ->
  store_closed (store_restrict σ (fv_tm left ∪ fv_tm right)) ->
  (must_terminating (lstore_instantiate_tm (lstore_lift_free σ) (choose_tm left right)) <->
    must_terminating (lstore_instantiate_tm (lstore_lift_free σ) left) /\
    must_terminating (lstore_instantiate_tm (lstore_lift_free σ) right)).
Proof.
  intros Hl Hr Hclosed. rewrite instantiate_lift_choose_tm by assumption.
  apply choose_tm_must_terminate.
  - eapply instantiate_lift_lc_on with (X := fv_tm left ∪ fv_tm right);
      [exact Hl|clear; set_solver|exact Hclosed].
  - eapply instantiate_lift_lc_on with (X := fv_tm left ∪ fv_tm right);
      [exact Hr|clear; set_solver|exact Hclosed].
Qed.

Lemma choose_tm_total_formula left right (m : WfWorldT) :
  lc_tm left -> lc_tm right ->
  wfworld_closed_on (fv_tm left ∪ fv_tm right) m ->
  m ⊨ expr_total_formula left -> m ⊨ expr_total_formula right ->
  m ⊨ expr_total_formula (choose_tm left right).
Proof.
  intros Hl Hr Hclosed Hleft Hright.
  apply expr_total_formula_models_iff in Hleft as [HscopeL [HlcL HstoresL]].
  apply expr_total_formula_models_iff in Hright as [HscopeR [HlcR HstoresR]].
  apply expr_total_formula_models_iff. split.
  - unfold formula_scoped_in_world in *.
    rewrite !formula_fv_expr_total_formula, !tm_lvars_fv in *.
    rewrite fv_choose_tm by assumption. clear -HscopeL HscopeR. set_solver.
  - split; [apply tm_lvars_lc, choose_tm_lc; assumption|].
    intros σ Hσ. apply (proj2 (choose_tm_store_total σ left right Hl Hr (Hclosed σ Hσ))).
    split; [apply HstoresL|apply HstoresR]; exact Hσ.
Qed.

Lemma choose_under_denotation gasL gasR gas Σ b φ left right (m : WfWorldT) :
  lty_env_closed Σ -> lc_tm left -> lc_tm right -> lc_context_ty (CTUnder b φ) ->
  m ⊨ ty_static_guard_formula Σ (CTUnder b φ) (choose_tm left right) ->
  m ⊨ ty_denote_gas gasL Σ (CTOver b qual_top) left ->
  m ⊨ ty_denote_gas (S gasR) Σ (CTUnder b φ) right ->
  m ⊨ ty_denote_gas gas Σ (CTUnder b φ) (choose_tm left right).
Proof.
  intros HΣ Hl Hr Hlc Hstatic Hleft Hright.
  assert (Hclosed : wfworld_closed_on (fv_tm left ∪ fv_tm right) m).
  { apply wfworld_closed_on_union.
    - exact (denot_ty_lvar_guard_wfworld_closed_on_term _ _ _ _
        (ty_denote_gas_guard _ _ _ _ _ Hleft)).
    - exact (denot_ty_lvar_guard_wfworld_closed_on_term _ _ _ _
        (ty_denote_gas_guard _ _ _ _ _ Hright)). }
  eapply under_denote_of_result_inclusion;
    [exact HΣ|exact Hr|exact Hlc|exact Hright| |].
  - apply ty_denote_gas_zero_of_guard.
    apply ty_guard_relevant_of_static_full_total; [exact Hstatic|].
    apply choose_tm_total_formula; try assumption.
    + exact (ty_guard_formula_total _ _ _ _ (ty_denote_gas_guard _ _ _ _ _ Hleft)).
    + exact (ty_guard_formula_total _ _ _ _ (ty_denote_gas_guard _ _ _ _ _ Hright)).
  - intros σ v Hσ Heval.
    apply (proj2 (choose_tm_store_results σ left right v Hl Hr (Hclosed σ Hσ))).
    right. exact Heval.
Qed.
