(** Conditional operational coverage and full base-under denotations.
    Coverage is a semantic auxiliary property, not a typing constructor. *)
From Denotation Require Import Notation TypeDenote TypeEquivCore
  TypeEquivFiberBaseCore TypeEquivBody TypePersistBase TypePersistWandForward
  BaseIntro ConditionalCoverage.
From ContextLogic Require Import FormulaUnderCoverage.

Lemma store_projection_eq_with_result (σ τ : StoreT) (S : aset) y :
  store_restrict σ S = store_restrict τ S ->
  σ !! y = τ !! y ->
  store_restrict σ (S ∪ {[y]}) = store_restrict τ (S ∪ {[y]}).
Proof.
  intros HS Hy. apply storeA_map_eq. intros x.
  rewrite !storeA_restrict_lookup.
  destruct (decide (x ∈ S ∪ {[y]})) as [Hx|Hx]; [|reflexivity].
  destruct (decide (x ∈ S)) as [HxS|HxS].
  - pose proof (f_equal (fun st : gmap atom value => st !! x) HS) as Hlook.
    change ((storeA_restrict σ S : gmap atom value) !! x =
      (storeA_restrict τ S : gmap atom value) !! x) in Hlook.
    pose proof (eq_trans
      (eq_sym (storeA_restrict_lookup (V:=value) (K:=atom) σ S x))
      (eq_trans Hlook (storeA_restrict_lookup (V:=value) (K:=atom) τ S x)))
      as Hdirect.
    destruct (decide (x ∈ S)); [exact Hdirect|contradiction].
  - assert (x = y) by (clear -Hx HxS; set_solver). subst x. exact Hy.
Qed.

(** A canonical result extension preserves the complete old projection.
    Completeness in an arbitrary result world only preserves the relevant
    domain; these two statements are deliberately kept separate. *)
Lemma under_denote_canonical_result_world gas Σ b φ e (m : WfWorldT) y :
  lty_env_closed Σ -> lc_tm e ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) e ->
  y ∉ world_dom (m : WorldT) ∪ qual_dom φ ->
  exists my : WfWorldT,
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    my ⊨ expr_result_formula_at (dom (relevant_env Σ (CTUnder b φ) e)) e (LVFree y) /\
    my ⊨ under_open_body b φ y.
Proof.
  intros HΣ Hlce Hden Hy.
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTUnder b φ) e).
  { apply ty_denote_gas_zero_of_guard.
    exact (ty_denote_gas_guard _ _ _ _ _ Hden). }
  set (D := dom (relevant_env Σ (CTUnder b φ) e)).
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
  exists my. split; [exact Hdom|]. split; [exact Hrestrict|].
  split; [exact Hresult|].
  eapply ty_denote_gas_under_result_body_elim;
    [exact HΣ|exact Hlce| | | | |exact Hdom|exact Hrestrict|exact Hresult|exact Hden].
  - clear -Hy. set_solver.
  - intros H. apply HeX, HDm in H. clear -H Hy. set_solver.
  - clear -HDm Hy. set_solver.
  - clear -Hy. set_solver.
Qed.

Lemma lifted_projection_eq_of_atom_projection (σ τ : StoreT) E :
  store_restrict σ (lvars_fv E) = store_restrict τ (lvars_fv E) ->
  storeA_restrict (lstore_lift_free σ) E =
    storeA_restrict (lstore_lift_free τ) E.
Proof.
  intros H.
  transitivity (storeA_restrict
    (lstore_lift_free (store_restrict σ (lvars_fv E))) E).
  - symmetry. apply lstore_lift_free_restrict_fv_lvars_eq.
  - rewrite H. apply lstore_lift_free_restrict_fv_lvars_eq.
Qed.

Lemma under_denote_intro_store_coverage gas Σ b φ e (m : WfWorldT) (L : aset) :
  lc_context_ty (CTUnder b φ) ->
  m ⊨ ty_denote_gas 0 Σ (CTUnder b φ) e ->
  (forall y, y ∉ L -> forall σ, (m : WorldT) σ -> exists τ,
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) τ /\
    store_restrict τ (qual_dom φ) = store_restrict σ (qual_dom φ)) ->
  (forall y, y ∉ L -> forall σ τ, (m : WorldT) σ ->
    store_restrict τ (qual_dom φ) = store_restrict σ (qual_dom φ) ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) τ ->
    exists σ' v, (m : WorldT) σ' /\
      store_restrict σ' (qual_dom φ) = store_restrict σ (qual_dom φ) /\
      τ !! y = Some v /\ tm_eval_in_store σ' e v) ->
  m ⊨ ty_denote_gas gas Σ (CTUnder b φ) e.
Proof.
  intros Hlc Hzero Hne Hcover.
  set (D := dom (relevant_env Σ (CTUnder b φ) e)).
  assert (HeD : tm_lvars e ⊆ D).
  { exact (ty_denote_gas_zero_tm_lvars_dom Σ (CTUnder b φ) e m Hzero). }
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  { exact (ty_denote_gas_zero_relevant_env_world Σ (CTUnder b φ) e m Hzero). }
  assert (HφD : qual_dom φ ⊆ lvars_fv D).
  { rewrite <- (context_ty_lvars_under_fv b φ).
    apply lvars_fv_mono.
    exact (ty_denote_gas_zero_context_lvars_dom Σ (CTUnder b φ) e m Hzero). }
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)) by (clear -HφD HDm; set_solver).
  assert (Hfvm : fv_tm e ⊆ world_dom (m : WorldT)).
  { rewrite <- tm_lvars_fv. etransitivity; [apply lvars_fv_mono; exact HeD|exact HDm]. }
  apply (base_refinement_intro false gas Σ b φ e m
    (L ∪ world_dom (m : WorldT) ∪ qual_dom φ)); [exact Hzero|].
  intros y my Hy Hiny Hdom Hrestrict Hresult.
  assert (HyL : y ∉ L) by (clear -Hy; set_solver).
  assert (Hyφ : y ∉ qual_dom φ) by (clear -Hy; set_solver).
  assert (HyD : LVFree y ∉ D).
  { intros H. apply lvars_fv_elem in H. apply HDm in H. clear -H Hy. set_solver. }
  cbn [polarity_open_body]. unfold under_open_body.
  set (E := qual_vars (qual_open_atom 0 y φ) ∖ {[LVFree y]}).
  set (q := qual_open_atom 0 y (typed_result_qual b φ)).
  assert (HE : lvars_fv E = qual_dom φ).
  { exact (base_result_parameters φ y Hyφ). }
  assert (Hq : qual_dom q = qual_dom φ ∪ {[y]}).
  { exact (opened_typed_base_qual_dom b φ y). }
  assert (Hlcq : lc_lvars (qual_vars q)).
  { exact (opened_typed_base_qual_lc b φ y Hlc Hyφ). }
  assert (HEq : E ⊆ qual_vars q).
  { unfold E, q. rewrite !qual_open_atom_vars.
    transitivity (lvars_open 0 y (qual_vars φ)).
    - intros u Hu. apply elem_of_difference in Hu. exact (proj1 Hu).
    -
    apply lvars_open_mono. cbn [typed_result_qual qual_vars qual_lvars]. set_solver. }
  assert (HlcE : lc_lvars E) by (intros u Hu; apply Hlcq; apply HEq; exact Hu).
  apply fib_under_atom_intro_store_coverage; [exact HlcE|exact Hlcq|exact HEq| | |].
  - unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom, HE.
    change (qual_dom φ ∪ qual_dom q ⊆ world_dom (my : WorldT)).
    rewrite Hq, Hdom.
    clear -Hφm. set_solver.
  - intros σy Hσy.
    assert (Hσ : (m : WorldT) (store_restrict σy (world_dom (m : WorldT)))).
    { rewrite <- Hrestrict. exists σy. split; [exact Hσy|].
      f_equal. rewrite res_restrict_dom, Hdom. clear; set_solver. }
    destruct (Hne y HyL _ Hσ) as [τ [Hτ Hτφ]].
    exists τ. split; [exact Hτ|]. rewrite HE.
    rewrite Hτφ, storeA_restrict_twice_subset by exact Hφm. reflexivity.
  - intros σy τ Hσy Hτφ Hτq. rewrite HE in Hτφ.
    assert (Hσ : (m : WorldT) (store_restrict σy (world_dom (m : WorldT)))).
    { rewrite <- Hrestrict. exists σy. split; [exact Hσy|].
      f_equal. rewrite res_restrict_dom, Hdom. clear; set_solver. }
    assert (Hτbase : store_restrict τ (qual_dom φ) =
        store_restrict (store_restrict σy (world_dom (m : WorldT))) (qual_dom φ)).
    { rewrite storeA_restrict_twice_subset by exact Hφm. exact Hτφ. }
    destruct (Hcover y HyL _ τ Hσ Hτbase Hτq)
      as [σ' [v [Hσ' [Hσ'φ [Hτy Heval]]]]].
    rewrite <- Hrestrict in Hσ'.
    destruct Hσ' as [σhat [Hσhat Hσhat_eq]].
    assert (Hhatbase : store_restrict σhat (world_dom (m : WorldT)) = σ').
    { exact Hσhat_eq. }
    assert (Hevalhat : tm_eval_in_store (store_restrict σhat (fv_tm e)) e v).
    { apply (proj2 (tm_eval_in_store_restrict_fv_exact σhat e v)).
      assert (Hagree : store_restrict σhat (fv_tm e) = store_restrict σ' (fv_tm e)).
      { rewrite <- Hhatbase, storeA_restrict_twice_subset by exact Hfvm. reflexivity. }
      apply (proj2 (tm_eval_in_store_agree_on_fv σhat σ' e v Hagree)). exact Heval. }
    destruct (expr_result_formula_at_fiber_witness D e y my HeD HyD
      Hresult σhat v Hσhat Hevalhat) as [σout [Hσout [HoutD Houty]]].
    assert (Houtφ : store_restrict σout (qual_dom φ) = store_restrict σy (qual_dom φ)).
    { transitivity (store_restrict σhat (qual_dom φ)).
      - eapply storeA_restrict_eq_mono with (Y := lvars_fv D); eauto.
      - rewrite <- Hhatbase in Hσ'φ.
        rewrite !storeA_restrict_twice_subset in Hσ'φ by exact Hφm. exact Hσ'φ. }
    exists σout. split; [exact Hσout|]. split; [rewrite HE; exact Houtφ|].
    apply lifted_projection_eq_of_atom_projection.
    change (store_restrict σout (qual_dom q) = store_restrict τ (qual_dom q)).
    rewrite Hq. apply store_projection_eq_with_result.
    + rewrite Houtφ. symmetry. exact Hτφ.
    + exact (eq_trans Houty (eq_sym Hτy)).
Qed.

Lemma under_denote_elim_store_coverage gas Σ b φ e (m : WfWorldT) y :
  lty_env_closed Σ -> lc_tm e -> lc_context_ty (CTUnder b φ) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) e ->
  y ∉ world_dom (m : WorldT) ∪ qual_dom φ ->
  (forall σ, (m : WorldT) σ -> exists τ,
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) τ /\
    store_restrict τ (qual_dom φ) = store_restrict σ (qual_dom φ)) /\
  (forall σ τ, (m : WorldT) σ ->
    store_restrict τ (qual_dom φ) = store_restrict σ (qual_dom φ) ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) τ ->
    exists σ' v, (m : WorldT) σ' /\
      store_restrict σ' (qual_dom φ) = store_restrict σ (qual_dom φ) /\
      τ !! y = Some v /\ tm_eval_in_store σ' e v).
Proof.
  intros HΣ Hlce Hlc Hden Hy.
  destruct (under_denote_canonical_result_world gas Σ b φ e m y
    HΣ Hlce Hden Hy) as [my [Hdom [Hrestrict [Hresult Hbody]]]].
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTUnder b φ) e).
  { apply ty_denote_gas_zero_of_guard.
    exact (ty_denote_gas_guard _ _ _ _ _ Hden). }
  set (D := dom (relevant_env Σ (CTUnder b φ) e)).
  pose proof (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hzero) as HeD.
  pose proof (ty_denote_gas_zero_relevant_env_world _ _ _ _ Hzero) as HDm.
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
  { rewrite <- (context_ty_lvars_under_fv b φ).
    exact (ty_denote_gas_type_lvars_world _ _ _ _ _ Hden). }
  assert (Hfvm : fv_tm e ⊆ world_dom (m : WorldT)).
  { rewrite <- tm_lvars_fv. etransitivity; [apply lvars_fv_mono; exact HeD|exact HDm]. }
  assert (Hyφ : y ∉ qual_dom φ) by (clear -Hy; set_solver).
  assert (HyD : LVFree y ∉ D).
  { intros H. apply lvars_fv_elem in H. apply HDm in H. clear -H Hy. set_solver. }
  set (E := qual_vars (qual_open_atom 0 y φ) ∖ {[LVFree y]}).
  set (q := qual_open_atom 0 y (typed_result_qual b φ)).
  assert (HE : lvars_fv E = qual_dom φ) by (apply base_result_parameters; exact Hyφ).
  assert (Hlcq : lc_lvars (qual_vars q)) by (apply opened_typed_base_qual_lc; assumption).
  assert (HEq : E ⊆ qual_vars q).
  { unfold E, q. rewrite !qual_open_atom_vars.
    transitivity (lvars_open 0 y (qual_vars φ)).
    - intros u Hu. apply elem_of_difference in Hu. exact (proj1 Hu).
    - apply lvars_open_mono. cbn [typed_result_qual qual_vars qual_lvars]. set_solver. }
  assert (Hlift : forall σ, (m : WorldT) σ -> exists σy,
    (my : WorldT) σy /\ store_restrict σy (qual_dom φ) = store_restrict σ (qual_dom φ)).
  { intros σ Hσ. rewrite <- Hrestrict in Hσ.
    destruct Hσ as [σy [Hσy Hσold]]. exists σy. split; [exact Hσy|].
    rewrite <- Hσold, storeA_restrict_twice_subset by exact Hφm. reflexivity. }
  split.
  - intros σ Hσ. destruct (Hlift σ Hσ) as [σy [Hσy Hσyφ]].
    destruct (fib_under_atom_inhabited_store my E q σy Hlcq HEq Hbody Hσy)
      as [τ [Hτ HτE]]. exists τ. split; [exact Hτ|].
    rewrite HE in HτE. rewrite HτE. exact Hσyφ.
  - intros σ τ Hσ Hτφ Hτq.
    destruct (Hlift σ Hσ) as [σy [Hσy Hσyφ]].
    destruct (fib_under_atom_covers_store my E q σy τ Hbody Hσy
      ltac:(rewrite HE, Hσyφ; exact Hτφ) Hτq)
      as [σout [Hσout [HoutE Houtq]]].
    pose proof (expr_result_formula_at_models_elim D e y my
      HeD HyD Hresult σout Hσout) as [_ [v [Houty Heval]]].
    rewrite lstore_lift_free_lookup_free in Houty.
    assert (Hτy : τ !! y = Some v).
    { rewrite <- lstore_lift_free_lookup_free.
      eapply storeA_restrict_lookup_transport;
        [|exact Houtq|rewrite lstore_lift_free_lookup_free; exact Houty].
      apply lvars_fv_elem. change (y ∈ qual_dom q).
      unfold q. rewrite opened_typed_base_qual_dom. clear; set_solver. }
    exists (store_restrict σout (world_dom (m : WorldT))), v. split.
    + rewrite <- Hrestrict. exists σout. split; [exact Hσout|].
      f_equal. rewrite res_restrict_dom, Hdom. clear; set_solver.
    + split.
      * rewrite storeA_restrict_twice_subset by exact Hφm.
        rewrite HE in HoutE. rewrite HoutE. exact Hσyφ.
      * split; [exact Hτy|].
        apply (proj2 (tm_eval_in_store_agree_on_fv
          (store_restrict σout (world_dom (m : WorldT))) σout e v
          ltac:(apply storeA_restrict_twice_subset; exact Hfvm))).
        exact Heval.
Qed.

(** Under coverage survives the addition of terminating results.  The target
    guard is explicit: result inclusion alone says nothing about divergent
    executions.  This is a semantic transport lemma, not an oracle rule. *)
Lemma under_denote_of_result_inclusion gas1 gas2 Σ b φ e1 e2 (m : WfWorldT) :
  lty_env_closed Σ -> lc_tm e1 -> lc_context_ty (CTUnder b φ) ->
  m ⊨ ty_denote_gas (S gas1) Σ (CTUnder b φ) e1 ->
  m ⊨ ty_denote_gas 0 Σ (CTUnder b φ) e2 ->
  (forall σ v, (m : WorldT) σ -> tm_eval_in_store σ e1 v ->
    tm_eval_in_store σ e2 v) ->
  m ⊨ ty_denote_gas gas2 Σ (CTUnder b φ) e2.
Proof.
  intros HΣ Hlce Hlc Hden Hzero Hincl.
  apply (under_denote_intro_store_coverage gas2 Σ b φ e2 m
    (world_dom (m : WorldT) ∪ qual_dom φ)); [exact Hlc|exact Hzero| |].
  - intros y Hy. exact (proj1 (under_denote_elim_store_coverage
      gas1 Σ b φ e1 m y HΣ Hlce Hlc Hden Hy)).
  - intros y Hy σ τ Hσ Hτφ Hτq.
    destruct (proj2 (under_denote_elim_store_coverage
      gas1 Σ b φ e1 m y HΣ Hlce Hlc Hden Hy) σ τ Hσ Hτφ Hτq)
      as [σ' [v [Hσ' [Hφ [Hyv Heval]]]]].
    exists σ', v. repeat split; try assumption. apply Hincl; assumption.
Qed.
