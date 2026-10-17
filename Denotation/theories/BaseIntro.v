(** Guarded base-refinement introduction from the opened result body. *)
From Denotation Require Import Context TypeEquivCore TypeEquivBody TypeEquivFiberBaseCore.

Definition polarity_ty (pol : bool) b φ : context_ty :=
  match pol with true => CTOver b φ | false => CTUnder b φ end.
Definition polarity_open_body (pol : bool) b φ r : FormulaT :=
  match pol with true => over_open_body b φ r | false => under_open_body b φ r end.

Lemma base_refinement_intro pol gas Σ b φ e (m : WfWorldT) (L : aset) :
  m ⊨ ty_denote_gas 0 Σ (polarity_ty pol b φ) e ->
  (forall r (my : WfWorldT), r ∉ L ->
    r ∈ world_dom (my : WorldT) ->
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[r]} ->
    res_restrict my (world_dom (m : WorldT)) = m ->
    my ⊨ expr_result_formula_at
      (dom (relevant_env Σ (polarity_ty pol b φ) e)) e (LVFree r) ->
    my ⊨ polarity_open_body pol b φ r) ->
  m ⊨ ty_denote_gas gas Σ (polarity_ty pol b φ) e.
Proof.
  intros Hzero Hbody.
  destruct gas as [|gas]; [exact Hzero|].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ
    (polarity_ty pol b φ) e m Hzero) as Hscope.
  pose proof (formula_scoped_and_r _ _ _ Hscope) as Hscope_forall.
  pose proof (ty_denote_gas_zero_lc_relevant_env Σ
    (polarity_ty pol b φ) e m Hzero) as HlcD.
  pose proof (ty_denote_gas_guard_of_zero Σ
    (polarity_ty pol b φ) e m Hzero) as Hguard.
  pose proof (ty_guard_formula_basic_typing _ _ _ m Hguard) as Hbasic.
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hbasic]].
  pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hbasic) as Hlce.
  destruct pol; cbn [polarity_ty polarity_open_body] in *;
    cbn [ty_denote_gas]; apply res_models_and_iff;
    split; [exact Hguard| |exact Hguard|];
    eapply res_models_forall_rev_intro; [exact Hscope_forall| |exact Hscope_forall|].
  all: exists (L ∪ qual_dom φ ∪ fv_tm e ∪
      lvars_fv (dom (relevant_env Σ (polarity_ty true b φ) e)) ∪
      world_dom (m : WorldT));
    intros r Hr my Hdom Hrestrict;
    assert (Hiny : r ∈ world_dom (my : WorldT)) by (clear -Hdom; rewrite Hdom; set_solver);
    assert (Hrφ : r ∉ qual_dom φ) by (clear -Hr; set_solver);
    pose proof (formula_scoped_forall_open_res_le m my r _ Hscope_forall
      (res_le_of_projection_eq _ _ Hrestrict) Hiny) as Hscope_open;
    rewrite formula_open_impl in Hscope_open |- *;
    eapply res_models_impl_intro; [exact Hscope_open|]; intros Hres;
    rewrite (formula_open_result_first_expr_result_formula_at_shift0
      r _ e HlcD) in Hres by (first [exact Hlce|clear -Hr; set_solver]).

  - change (my ⊨ formula_open 0 r
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (over_result_body b φ))).
    rewrite formula_open_over_typed_body_normalize by (intros Hin; apply Hrφ; apply lvars_fv_elem; exact Hin).
    apply over_open_body_to_typed; [exact Hiny|].
    eapply Hbody; eauto. clear -Hr; set_solver.
  - change (my ⊨ formula_open 0 r
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (under_result_body b φ))).
    rewrite formula_open_under_typed_body_normalize by (intros Hin; apply Hrφ; apply lvars_fv_elem; exact Hin).
    apply under_open_body_to_typed; [exact Hiny|].
    eapply Hbody; eauto. clear -Hr; set_solver.
Qed.
