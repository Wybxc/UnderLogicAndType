(** Store-level Over consequences transport an existing denotation.
    Unlike Under support changes, they need no globally fixed parameters. *)
From Denotation Require Import Notation TypeDenote TypeDenoteRegular
  TypeEquivCore TypeEquivFiberBaseCore TypePersistBase TypePersistWandForward
  BaseIntro BaseCoverage ConditionalCoverage QualifierStore.
From ContextLogic Require Import FormulaUnderCoverage.

Lemma over_open_body_intro_store_holds b φ y (m : WfWorldT) :
  lc_context_ty (CTUnder b φ) -> y ∉ qual_dom φ ->
  qual_dom φ ∪ {[y]} ⊆ world_dom (m : WorldT) ->
  (forall σ, (m : WorldT) σ ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) σ) ->
  m ⊨ over_open_body b φ y.
Proof.
  intros Hlc Hy Hscope Hholds. unfold over_open_body.
  set (E := qual_vars (qual_open_atom 0 y φ) ∖ {[LVFree y]}).
  set (q := qual_open_atom 0 y (typed_result_qual b φ)).
  assert (HEq : E ⊆ qual_vars q).
  { unfold E, q. rewrite !qual_open_atom_vars.
    transitivity (lvars_open 0 y (qual_vars φ)).
    - intros x Hx. apply elem_of_difference in Hx. exact (proj1 Hx).
    - apply lvars_open_mono. cbn [typed_result_qual qual_vars qual_lvars]. set_solver. }
  assert (Hlcq : lc_lvars (qual_vars q)) by (apply opened_typed_base_qual_lc; assumption).
  assert (HlcE : lc_lvars E) by (intros x Hx; apply Hlcq; apply HEq; exact Hx).
  assert (Hqscope : qual_dom q ⊆ world_dom (m : WorldT)).
  { unfold q. rewrite opened_typed_base_qual_dom. exact Hscope. }
  apply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    change (lvars_fv E ∪ qual_dom q ⊆ world_dom (m : WorldT)).
    pose proof (lvars_fv_mono E (qual_vars q) HEq). clear -Hqscope H. set_solver.
  - exact HlcE.
  - intros σfix mfib Hfib.
    change (mfib ⊨ FOver (FAtom (qual_msubst_store σfix q))).
    apply res_models_over_FAtom_intro_store_holds.
    + change (formula_scoped_in_world mfib
        (formula_msubst_store σfix (FOver (FAtom q)))).
      unfold formula_scoped_in_world.
      etransitivity; [apply formula_msubst_store_fv_subset|].
      rewrite formula_fv_over, formula_fv_atom.
      rewrite (res_fiber_from_projection_world_dom m mfib _ _ Hfib).
      exact Hqscope.
    + intros σ Hσ. apply qualifier_msubst_store_holds_of_restrict.
      * eapply res_fiber_from_projection_store_restrict; eassumption.
      * apply Hholds. eapply res_fiber_from_projection_store_source; eassumption.
Qed.

Lemma over_denote_intro_store_results gas Σ b φ e (m : WfWorldT) (L : aset) :
  lc_context_ty (CTOver b φ) ->
  m ⊨ ty_denote_gas 0 Σ (CTOver b φ) e ->
  (forall y, y ∉ L -> forall σ v, (m : WorldT) σ -> tm_eval_in_store σ e v ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) (<[y:=v]> σ)) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b φ) e.
Proof.
  intros Hlc Hzero Hholds.
  set (D := dom (relevant_env Σ (CTOver b φ) e)).
  pose proof (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hzero) as HeD.
  pose proof (ty_denote_gas_zero_relevant_env_world _ _ _ _ Hzero) as HDm.
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
  { rewrite <- (context_ty_lvars_over_fv b φ).
    exact (ty_denote_gas_type_lvars_world _ _ _ _ _ Hzero). }
  assert (Hfvm : fv_tm e ⊆ world_dom (m : WorldT)).
  { rewrite <- tm_lvars_fv. etransitivity; [apply lvars_fv_mono; exact HeD|exact HDm]. }
  apply (base_refinement_intro true gas Σ b φ e m
    (L ∪ world_dom (m : WorldT) ∪ qual_dom φ)); [exact Hzero|].
  intros y my Hy Hiny Hdom Hrestrict Hresult.
  assert (HyL : y ∉ L) by (clear -Hy; set_solver).
  assert (Hyφ : y ∉ qual_dom φ) by (clear -Hy; set_solver).
  assert (HyD : LVFree y ∉ D).
  { intros H. apply lvars_fv_elem in H. apply HDm in H. clear -H Hy. set_solver. }
  cbn [polarity_open_body]. apply over_open_body_intro_store_holds.
  - exact Hlc.
  - exact Hyφ.
  - rewrite Hdom. clear -Hφm. set_solver.
  - intros σy Hσy.
    set (σ := store_restrict σy (world_dom (m : WorldT))).
    assert (Hσ : (m : WorldT) σ).
    { rewrite <- Hrestrict. exists σy. split; [exact Hσy|].
      unfold σ. reflexivity. }
    pose proof (expr_result_formula_at_models_elim D e y my HeD HyD Hresult σy Hσy)
      as [_ [v [Hyv Heval]]].
    rewrite lstore_lift_free_lookup_free in Hyv.
    assert (Hevalσ : tm_eval_in_store σ e v).
    { assert (Hagree : store_restrict σ (fv_tm e) = store_restrict σy (fv_tm e)).
      { unfold σ. apply storeA_restrict_twice_subset. exact Hfvm. }
      apply (proj2 (tm_eval_in_store_agree_on_fv σ σy e v Hagree)). exact Heval. }
    pose proof (Hholds y HyL σ v Hσ Hevalσ) as Hq.
    eapply qualifier_holds_store_eq_on; [|exact Hq].
    rewrite opened_typed_base_qual_dom. apply store_projection_eq_with_result.
    + rewrite store_insert_restrict_notin by exact Hyφ.
      unfold σ. apply storeA_restrict_twice_subset. exact Hφm.
    + exact (eq_trans (map_lookup_insert σ y v) (eq_sym Hyv)).
Qed.

Lemma over_denote_canonical_result_world gas Σ b φ e (m : WfWorldT) y :
  lty_env_closed Σ -> lc_tm e ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) e ->
  y ∉ world_dom (m : WorldT) ∪ qual_dom φ ->
  exists my : WfWorldT,
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    my ⊨ expr_result_formula_at (dom (relevant_env Σ (CTOver b φ) e)) e (LVFree y) /\
    my ⊨ over_open_body b φ y.
Proof.
  intros HΣ Hlce Hden Hy.
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTOver b φ) e).
  { apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hden). }
  set (D := dom (relevant_env Σ (CTOver b φ) e)).
  pose proof (ty_denote_gas_zero_lc_relevant_env _ _ _ _ Hzero) as HlcD.
  pose proof (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hzero) as HeD.
  pose proof (ty_denote_gas_zero_relevant_env_world _ _ _ _ Hzero) as HDm.
  assert (HeX : fv_tm e ⊆ lvars_fv D).
  { rewrite <- tm_lvars_fv. apply lvars_fv_mono. exact HeD. }
  assert (HyD : LVFree y ∉ D).
  { intros H. apply lvars_fv_elem in H. apply HDm in H. clear -H Hy. set_solver. }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv D) e y HeX ltac:(clear -HDm Hy; set_solver)) as [F HF].
  destruct (res_extend_by_exists m F) as [my Hext].
  { constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)).
      destruct HF as [_ _ [Hin _] _]. rewrite Hin. exact HDm.
    - change (ext_out F ## world_dom (m : WorldT)).
      destruct HF as [_ _ [_ Hout] _]. rewrite Hout. clear -Hy. set_solver. }
  pose proof HF as [_ _ [_ Hout] _].
  destruct (res_extend_by_singleton_output_open_world m my F y Hext Hout)
    as [Hdom Hrestrict].
  assert (Hresult : my ⊨ expr_result_formula_at D e (LVFree y)).
  { eapply expr_result_formula_at_of_result_extends_on;
      [exact HlcD|exact HeD|exact HyD|exact HDm|exact HF|exact Hext|].
    exact (ty_denote_gas_zero_total_atom_world _ _ _ _ Hzero). }
  exists my. split; [exact Hdom|]. split; [exact Hrestrict|]. split; [exact Hresult|].
  eapply ty_denote_gas_over_result_body_elim;
    [exact HΣ|exact Hlce| | | | |exact Hdom|exact Hrestrict|exact Hresult|exact Hden].
  - clear -Hy. set_solver.
  - intros H. apply HeX, HDm in H. clear -H Hy. set_solver.
  - clear -HDm Hy. set_solver.
  - clear -Hy. set_solver.
Qed.

Lemma over_denote_elim_store_results gas Σ b φ e (m : WfWorldT) y :
  lty_env_closed Σ -> lc_tm e ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) e ->
  y ∉ world_dom (m : WorldT) ∪ qual_dom φ ->
  forall σ v, (m : WorldT) σ -> tm_eval_in_store σ e v ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) (<[y:=v]> σ).
Proof.
  intros HΣ Hlce Hden Hy σ v Hσ Heval.
  destruct (over_denote_canonical_result_world gas Σ b φ e m y HΣ Hlce Hden Hy)
    as [my [Hdom [Hrestrict [Hresult Hbody]]]].
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTOver b φ) e).
  { apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hden). }
  set (D := dom (relevant_env Σ (CTOver b φ) e)).
  pose proof (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hzero) as HeD.
  pose proof (ty_denote_gas_zero_relevant_env_world _ _ _ _ Hzero) as HDm.
  assert (HφD : qual_dom φ ⊆ lvars_fv D).
  { rewrite <- (context_ty_lvars_over_fv b φ). apply lvars_fv_mono.
    exact (ty_denote_gas_zero_context_lvars_dom _ _ _ _ Hzero). }
  assert (Hfvm : fv_tm e ⊆ world_dom (m : WorldT)).
  { rewrite <- tm_lvars_fv. etransitivity; [apply lvars_fv_mono; exact HeD|exact HDm]. }
  assert (HyD : LVFree y ∉ D).
  { intros H. apply lvars_fv_elem in H. apply HDm in H. clear -H Hy. set_solver. }
  rewrite <- Hrestrict in Hσ. destruct Hσ as [σbase [Hσbase Hbase]].
  assert (Hbase_old : store_restrict σbase (world_dom (m : WorldT)) = σ).
  { exact Hbase. }
  assert (Hevalbase : tm_eval_in_store (store_restrict σbase (fv_tm e)) e v).
  { apply (proj2 (tm_eval_in_store_restrict_fv_exact σbase e v)).
    assert (Hagree : store_restrict σbase (fv_tm e) = store_restrict σ (fv_tm e)).
    { rewrite <- Hbase_old, storeA_restrict_twice_subset by exact Hfvm. reflexivity. }
    apply (proj2 (tm_eval_in_store_agree_on_fv σbase σ e v Hagree)). exact Heval. }
  destruct (expr_result_formula_at_fiber_witness D e y my HeD HyD Hresult
    σbase v Hσbase Hevalbase) as [σout [Hσout [HoutD Houty]]].
  pose proof (fib_over_atom_store_holds my _ _ Hbody σout Hσout) as Hq.
  eapply opened_typed_qualifier_normalize; [clear -Hy; set_solver| |exact Houty|exact Hq].
  transitivity (store_restrict σbase (qual_dom φ)).
  - eapply storeA_restrict_eq_mono; eassumption.
  - rewrite <- Hbase_old, storeA_restrict_twice_subset by (clear -HφD HDm; set_solver).
    reflexivity.
Qed.

Lemma over_denote_store_consequence gas1 gas2 Σ b φ1 φ2 e (m : WfWorldT) :
  lty_env_closed Σ -> lc_tm e -> lc_context_ty (CTOver b φ2) ->
  m ⊨ ty_denote_gas (S gas1) Σ (CTOver b φ1) e ->
  m ⊨ ty_denote_gas 0 Σ (CTOver b φ2) e ->
  (forall y σ v, y ∉ world_dom (m : WorldT) ∪ qual_dom φ1 ∪ qual_dom φ2 ->
    (m : WorldT) σ ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ1)) (<[y:=v]> σ) ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ2)) (<[y:=v]> σ)) ->
  m ⊨ ty_denote_gas gas2 Σ (CTOver b φ2) e.
Proof.
  intros HΣ Hlce Hlc2 Hsource Hzero Hmap.
  apply (over_denote_intro_store_results gas2 Σ b φ2 e m
    (world_dom (m : WorldT) ∪ qual_dom φ1 ∪ qual_dom φ2));
    [exact Hlc2|exact Hzero|].
  intros y Hy σ v Hσ Heval. apply Hmap; [exact Hy|exact Hσ|].
  eapply over_denote_elim_store_results;
    [exact HΣ|exact Hlce|exact Hsource| |exact Hσ|exact Heval].
  clear -Hy. set_solver.
Qed.
