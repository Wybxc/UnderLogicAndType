(** Elimination of type-level persistence, including higher-order types. *)
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeEquivBody
  TypeEquivTermBase TypeEquivFiberTransport TypeEquivFiberBaseCore
  TypePersistBase ResultFirstOpen.

Lemma ty_guard_from_persist Σ τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTPersist τ) e) (CTPersist τ) e ->
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  rewrite relevant_env_persist_eq.
  unfold ty_guard_formula. repeat rewrite res_models_and_iff.
  intros [Hwf [Hworld [Hbasic Htotal]]].
  split; [|split; [exact Hworld|]; split; assumption].
  apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom Hτ]].
  apply context_ty_wf_formula_models_iff.
  split; [exact Hlc|]. split; [exact Hdom|exact Hτ].
Qed.

Lemma ty_denote_gas_insert_irrelevant gas Σ τ e y T :
  y ∉ fv_cty τ ∪ fv_tm e ->
  ty_denote_gas gas (<[LVFree y := T]> (relevant_env Σ τ e)) τ e =
  ty_denote_gas gas Σ τ e.
Proof.
  intros Hy. apply ty_denote_gas_env_agree_on with
    (X := context_ty_lvars τ ∪ tm_lvars e); [reflexivity|].
  unfold lty_env_restrict_lvars, relevant_env, relevant_lvars.
  rewrite storeA_restrict_insert_notin.
  - apply storeA_restrict_twice_same.
  - intros Hin. apply Hy. rewrite <- context_ty_lvars_fv, <- tm_lvars_fv.
    rewrite <- lvars_fv_union. apply lvars_fv_elem. exact Hin.
Qed.

Lemma ty_denote_gas_persist_open_alias gas Σ τ e y (m my : WfWorldT) :
  lty_env_closed Σ -> lc_tm e -> lc_context_ty τ ->
  y ∉ fv_tm e ∪ fv_cty τ ∪ lvars_fv (dom (relevant_env Σ τ e)) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) e ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ expr_result_formula_at (dom (relevant_env Σ τ e)) e (LVFree y) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τ]> (relevant_env Σ τ e)) τ (tret (vfvar y)).
Proof.
  intros HΣ He Hτ Hy Hden Hym Hdom Hrestrict Hres.
  pose proof (ty_denote_gas_persist_open_result gas Σ τ e y m my
    HΣ He ltac:(clear -Hy; set_solver)
    ltac:(rewrite relevant_env_persist_eq; clear -Hy; set_solver)
    Hden Hym Hdom Hrestrict ltac:(rewrite relevant_env_persist_eq; exact Hres)) as Hopen.
  rewrite formula_open_persist in Hopen.
  rewrite formula_open_ty_denote_gas_singleton in Hopen.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom, relevant_env_persist_eq.
      clear -Hy. set_solver. }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{ rewrite cty_shift_fv. clear -Hy. set_solver. }
  rewrite cty_open_shift_from_lc_fresh in Hopen by
    (exact Hτ || clear -Hy; set_solver).
  apply res_models_persist_elim in Hopen.
  rewrite typed_lty_env_bind_open_current in Hopen.
  - rewrite relevant_env_persist_eq in Hopen. exact Hopen.
  - rewrite relevant_env_persist_eq. intros Hbad.
    apply (proj2 (lvars_fv_elem _ _) ) in Hbad.
    clear -Hy Hbad. set_solver.
  - apply relevant_env_closed. exact HΣ.
Qed.

(** A fresh alias of a returned variable preserves its whole context type,
    including arrows.  No stability under deletion of stores is assumed. *)
Lemma ty_denote_gas_persist_ret_fvar_elim gas Σ τ z (m : WfWorldT) :
  lty_env_closed Σ -> lc_context_ty τ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) (tret (vfvar z)) ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar z)).
Proof.
  intros HΣ Hτ Hden.
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ τ (tret (vfvar z))).
  { apply ty_denote_gas_zero_of_guard_formula.
    apply ty_guard_from_persist.
    exact (ty_denote_gas_guard_formula _ _ _ _ _ Hden). }
  set (D := dom (relevant_env Σ τ (tret (vfvar z)))).
  pose proof (ty_denote_gas_zero_lc_relevant_env _ _ _ _ Hzero) as HlcD.
  pose proof (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hzero) as HeD.
  pose proof (ty_denote_gas_zero_relevant_env_world _ _ _ _ Hzero) as HDm.
  set (y := fresh_for (world_dom (m : WorldT) ∪ fv_cty τ ∪
    lvars_fv D ∪ {[z]})).
  assert (Hy : y ∉ world_dom (m : WorldT) ∪ fv_cty τ ∪
    lvars_fv D ∪ {[z]}) by (subst y; apply fresh_for_not_in).
  assert (HyD : LVFree y ∉ D).
  { intros H. apply (proj2 (lvars_fv_elem _ _)) in H. clear -Hy H. set_solver. }
  assert (HeX : fv_tm (tret (vfvar z)) ⊆ lvars_fv D).
  { rewrite <- tm_lvars_fv. intros x Hx.
    apply lvars_fv_elem. apply HeD. apply lvars_fv_elem. exact Hx. }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv D) (tret (vfvar z)) y HeX ltac:(clear -Hy; set_solver))
    as [F HF].
  destruct (res_extend_by_exists m F) as [my Hext].
  { constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)).
      destruct HF as [_ _ [Hin _] _]. rewrite Hin. exact HDm.
    - change (ext_out F ## world_dom (m : WorldT)).
      destruct HF as [_ _ [_ Hout] _]. rewrite Hout. clear -Hy. set_solver. }
  pose proof HF as [_ _ [_ Hout] _].
  destruct (res_extend_by_singleton_output_open_world m my F y Hext Hout)
    as [Hdom Hrestrict].
  assert (Hres : my ⊨ expr_result_formula_at D (tret (vfvar z)) (LVFree y)).
  { eapply expr_result_formula_at_of_result_extends_on;
      [exact HlcD|exact HeD|exact HyD|exact HDm|exact HF|exact Hext|].
    apply expr_total_formula_to_atom_world.
    exact (ty_denote_gas_total_guard_of_zero _ _ _ _ Hzero). }
  assert (Hinner : my ⊨ ty_denote_gas gas
      (<[LVFree y := erase_ty τ]> (relevant_env Σ τ (tret (vfvar z))))
      τ (tret (vfvar y))).
  { eapply ty_denote_gas_persist_open_alias;
      [exact HΣ|constructor; constructor|exact Hτ| |exact Hden| |exact Hdom|exact Hrestrict|exact Hres].
    - cbn [fv_tm fv_value]. clear -Hy. set_solver.
    - clear -Hy. set_solver. }
  set (Σy := <[LVFree y := erase_ty τ]>
    (relevant_env Σ τ (tret (vfvar z)))) in *.
  assert (Hzeroz : my ⊨ ty_denote_gas 0 Σy τ (tret (vfvar z))).
  { subst Σy. rewrite ty_denote_gas_insert_irrelevant.
    - eapply res_models_lift_projection_eq; eauto.
    - cbn [fv_tm fv_value]. clear -Hy. set_solver. }
  assert (Hzeroy : my ⊨ ty_denote_gas 0 Σy τ (tret (vfvar y))).
  { apply ty_denote_gas_zero_of_guard_formula.
    exact (ty_denote_gas_guard_formula _ _ _ _ _ Hinner). }
  assert (Hclosed : wfworld_closed_on
      (fv_tm (tret (vfvar y)) ∪ fv_tm (tret (vfvar z))) my).
  { apply wfworld_closed_on_union.
    - exact (denot_ty_lvar_guard_wfworld_closed_on_term
        (relevant_env Σy τ (tret (vfvar y))) τ (tret (vfvar y)) my
        (ty_denote_gas_guard_formula 0 Σy τ (tret (vfvar y)) my Hzeroy)).
    - exact (denot_ty_lvar_guard_wfworld_closed_on_term
        (relevant_env Σy τ (tret (vfvar z))) τ (tret (vfvar z)) my
        (ty_denote_gas_guard_formula 0 Σy τ (tret (vfvar z)) my Hzeroz)). }
  assert (Hres_small : my ⊨ expr_result_formula (tret (vfvar z)) (LVFree y)).
  { unfold expr_result_formula.
    eapply expr_result_formula_at_coarsen_domain;
      [exact HeD|reflexivity|exact HyD|exact Hres]. }
  pose proof (typed_total_equiv_ret_value_result_alias Σy τ my (vfvar z) y
    Hclosed ltac:(constructor) Hres_small Hzeroz Hzeroy) as Heq.
  assert (Hback : typed_total_equiv_on Σy τ my
    (tret (vfvar y)) (tret (vfvar z))).
  { destruct Heq as [Heq [Htotal [H0z H0y]]].
    split; [intros σ v Hσ; symmetry; apply Heq; exact Hσ|].
    split; [intros σ Hσ; symmetry; apply Htotal; exact Hσ|].
    split; assumption. }
  pose proof (ty_denote_gas_tm_equiv gas Σy τ _ _ my Hback Hinner) as Hmy.
  subst Σy. rewrite ty_denote_gas_insert_irrelevant in Hmy.
  2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
  pose proof (proj1 (res_models_minimal_on (world_dom (m : WorldT)) my
    (ty_denote_gas gas Σ τ (tret (vfvar z)))
    ltac:(eapply ty_denote_gas_scope_from_zero_any; exact Hzero)) Hmy) as Hproject.
  rewrite Hrestrict in Hproject. exact Hproject.
Qed.
