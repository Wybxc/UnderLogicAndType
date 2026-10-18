(** Context-typing derivations for the arithmetic library. *)
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From CaseStudy Require Import NatArithmetic NatArithmeticInstances NatArithmeticStages ArithmeticProofTools.
From Denotation Require Import Context ConstDenote ConstDenoteBase
  TypeEquiv TypeEquivCore TypeEquivTermBase TypeEquivBody TypeEquivFiberBaseCore BaseIntro.
From ContextTyping Require Import Typing TypingRegular NatCases Conversion
  Subtyping SoundnessLam SoundnessVar Soundness.

Definition q_nat_graph (f : nat -> nat -> nat) (u v w : logic_var) : type_qualifier :=
  tqual ({[u]} ∪ {[v]} ∪ {[w]})
    (fun s => exists n k,
      lso_store s !! u = Some (vnat n) /\
      lso_store s !! v = Some (vnat k) /\
      lso_store s !! w = Some (vnat (f n k))).

Lemma q_nat_graph_open f u v w j z :
  qual_open_atom j z (q_nat_graph f u v w) =
  q_nat_graph f (swap (LVBound j) (LVFree z) u)
    (swap (LVBound j) (LVFree z) v) (swap (LVBound j) (LVFree z) w).
Proof.
  apply qual_ext.
  - cbn [qual_open_atom q_nat_graph qual_lvars].
    rewrite !set_swap_union, !set_swap_singleton. reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_open_atom q_nat_graph qual_prop qual_lvars].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value.
    setoid_rewrite Hs. reflexivity.
Qed.

Lemma q_nat_graph_typed f u v :
  typed_result_qual TNat (q_nat_graph f u v (LVBound 0)) =
  q_nat_graph f u v (LVBound 0).
Proof.
  apply qual_ext.
  - cbn [typed_result_qual q_nat_graph qual_lvars qual_vars]. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [typed_result_qual q_nat_graph qual_prop qual_lvars qual_vars].
    unfold lstore_on_restrict, storeA_on_restrict.
    cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by set_solver.
    setoid_rewrite Hs.
    split; [tauto|]. intros [n [k [Hu [Hv Hw]]]].
    split.
    + exists n,k. auto.
    + exists (vnat (f n k)). split; [exact Hw|constructor].
Qed.

Lemma q_nat_graph_subst f x y r σ n k :
  σ !! x = Some (vnat n) -> σ !! y = Some (vnat k) ->
  dom (σ : gmap atom value) = {[x;y]} -> r ∉ ({[x;y]} : aset) ->
  qual_msubst_store σ (q_nat_graph f (LVFree x) (LVFree y) (LVFree r)) =
  mk_q_eq (vfvar r) (vnat (f n k)).
Proof.
  intros Hx Hy Hdom Hr.
  apply qual_ext.
  - cbn [qual_msubst_store qual_mlsubst q_nat_graph mk_q_eq qual_lvars
      lvar_value_keys].
    rewrite atom_store_to_lvar_store_dom, Hdom.
    unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver.
  - intros [ss1 Hd1] [ss2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [qual_msubst_store qual_mlsubst q_nat_graph mk_q_eq qual_prop
      qual_lvars lvar_value_keys denote_lvar_value].
    unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    set (D := ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]} : lvset)).
    assert (Hsx : (ss1 : gmap logic_var value) !! LVFree x = None).
    { apply not_elem_of_dom. rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_nat_graph qual_lvars].
      rewrite atom_store_to_lvar_store_dom, Hdom.
      unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver. }
    assert (Hsy : (ss1 : gmap logic_var value) !! LVFree y = None).
    { apply not_elem_of_dom. rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_nat_graph qual_lvars].
      rewrite atom_store_to_lvar_store_dom, Hdom.
      unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver. }
    assert (Hsr : LVFree r ∈ dom (ss1 : gmap logic_var value)).
    { rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_nat_graph qual_lvars].
      rewrite atom_store_to_lvar_store_dom, Hdom.
      unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver. }
    cbn [lso_store storeAO_store] in *.
    rewrite (lookup_union_r (M:=gmap logic_var) _ _ _ Hsx), (lookup_union_r (M:=gmap logic_var) _ _ _ Hsy).
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by (unfold D; set_solver).
    setoid_rewrite atom_store_to_lvar_store_lookup_free.
    setoid_rewrite Hx. setoid_rewrite Hy.
    apply elem_of_dom in Hsr.
    setoid_rewrite (lookup_union_l' (M:=gmap logic_var) ss1
      (storeA_restrict (atom_store_to_lvar_store σ) D) (LVFree r) Hsr).
    setoid_rewrite Hs.
    split.
    + intros [a [b [Ha [Hb Hab]]]]. inversion Ha; inversion Hb; subst. exact Hab.
    + intros H. exists n,k. auto.
Qed.

Lemma lookup_from_extension (m my : WfWorldT) x v :
  res_restrict my (world_dom (m : WorldT)) = m ->
  (forall s, (m : WorldT) s -> s !! x = Some v) ->
  forall s, (my : WorldT) s -> s !! x = Some v.
Proof.
  intros Hext Hlookup s Hs.
  assert (Hm : (m : WorldT) (store_restrict s (world_dom (m : WorldT)))).
  { rewrite <- Hext at 1. exists s. split; [exact Hs|reflexivity]. }
  specialize (Hlookup _ Hm).
  exact (proj2 (storeA_restrict_lookup_some _ _ _ _ Hlookup)).
Qed.

Lemma lookup_in_projection (m mfib : WfWorldT) X σ x v :
  x ∈ X -> res_fiber_from_projection m X σ mfib ->
  (forall s, (m : WorldT) s -> s !! x = Some v) -> σ !! x = Some v.
Proof.
  intros Hx Hfib Hlookup.
  destruct (world_wf mfib) as [[s Hs] _].
  pose proof (res_fiber_from_projection_store_source m mfib X σ s Hfib Hs) as Hsm.
  pose proof (res_fiber_from_projection_store_restrict_input m mfib X σ s Hfib Hs) as Heq.
  pose proof (storeA_restrict_lookup_some_2 s X x v (Hlookup s Hsm) Hx) as H.
  change ((store_restrict s X : gmap atom value) !! x = Some v) in H.
  rewrite Heq in H. exact H.
Qed.

Lemma result_at_const_lookup D c r (m : WfWorldT) :
  LVFree r ∉ D ->
  m ⊨ expr_result_formula_at D (tret (vconst c)) (LVFree r) ->
  forall s, (m : WorldT) s -> s !! r = Some (vconst c).
Proof.
  intros Hr Hres s Hs.
  destruct (expr_result_formula_at_models_elim D (tret (vconst c)) r m
    ltac:(cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys]; set_solver)
    Hr Hres s Hs) as [_ [v [Hv Heval]]].
  rewrite lstore_lift_free_lookup_free in Hv.
  unfold expr_eval_in_store in Heval.
  rewrite instantiate_closed_tm in Heval by reflexivity.
  apply val_steps_self in Heval. inversion Heval; subst. exact Hv.
Qed.

Lemma nat_graph_exact_open_body pol f x y r n k (m : WfWorldT) :
  r ∉ ({[x;y]} : aset) ->
  (forall s, (m : WorldT) s -> s !! x = Some (vnat n)) ->
  (forall s, (m : WorldT) s -> s !! y = Some (vnat k)) ->
  (forall s, (m : WorldT) s -> s !! r = Some (vnat (f n k))) ->
  m ⊨ polarity_open_body pol TNat
    (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)) r.
Proof.
  intros Hr Hx Hy Hlookr.
  assert (Hrx : r <> x) by set_solver.
  assert (Hry : r <> y) by set_solver.
  assert (Hdomxy : ({[x;y]} : aset) ⊆ world_dom (m : WorldT)).
  { destruct (world_wf m) as [[s Hs] _].
    pose proof (wfworld_store_dom m s Hs) as Hd.
    assert (Hsx : x ∈ dom (s : gmap atom value)) by (apply elem_of_dom; eauto).
    assert (Hsy : y ∈ dom (s : gmap atom value)) by (apply elem_of_dom; eauto).
    rewrite Hd in Hsx, Hsy. set_solver. }
  assert (Hdomr : r ∈ world_dom (m : WorldT)).
  { destruct (world_wf m) as [[s Hs] _].
    rewrite <- (wfworld_store_dom m s Hs). apply elem_of_dom. eauto. }
  destruct pol; cbn [polarity_open_body];
    unfold over_open_body, under_open_body;
    rewrite q_nat_graph_typed, !q_nat_graph_open;
    base_swap_normalize;
    replace (qual_vars (q_nat_graph f (LVFree x) (LVFree y) (LVFree r)) ∖
      {[LVFree r]}) with ({[LVFree x;LVFree y]} : lvset)
      by (cbn [q_nat_graph qual_vars qual_lvars]; set_solver);
    eapply res_models_FFibVars_intro.
  1,4: unfold formula_scoped_in_world;
    rewrite formula_fv_fibvars;
    first [rewrite formula_fv_over|rewrite formula_fv_under];
    rewrite formula_fv_atom;
    cbn [qual_dom qual_vars q_nat_graph qual_lvars];
    rewrite !lvars_fv_union, !lvars_fv_singleton_free; clear -Hdomxy Hdomr; set_solver.
  1,3: intros [j|z] Hz; cbn [lc_logic_var_key]; [set_solver|exact I].
  all: intros σ mfib Hfib;
    rewrite !lvars_fv_union, !lvars_fv_singleton_free in Hfib;
    assert (Hdomσ : dom (σ : gmap atom value) = {[x;y]}) by
      (pose proof (wfworld_store_dom (res_restrict m {[x;y]}) σ (proj1 Hfib)) as H;
       cbn in H; rewrite H; set_solver);
    assert (Hσx : σ !! x = Some (vnat n)) by
      (eapply (lookup_in_projection m mfib {[x;y]} σ x (vnat n));
       [set_solver|exact Hfib|exact Hx]);
    assert (Hσy : σ !! y = Some (vnat k)) by
      (eapply (lookup_in_projection m mfib {[x;y]} σ y (vnat k));
       [set_solver|exact Hfib|exact Hy]);
    first [change (mfib ⊨ FOver (FAtom (qual_msubst_store σ
      (q_nat_graph f (LVFree x) (LVFree y) (LVFree r))))) |
      change (mfib ⊨ FUnder (FAtom (qual_msubst_store σ
      (q_nat_graph f (LVFree x) (LVFree y) (LVFree r)))))];
    rewrite (q_nat_graph_subst f x y r σ n k Hσx Hσy Hdomσ Hr);
    first [apply res_models_over_intro_same_from_model|
      apply res_models_under_intro_same_from_model];
    apply const_type_qualifier_open_from_lookup;
    intros s Hs; apply Hlookr;
    eapply res_fiber_from_projection_store_source; eauto.
Qed.

Definition nat_graph_ty f x y :=
  precise_ty TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)).

Lemma nat_graph_wf d D f x y :
  x ∈ D -> y ∈ D -> wf_context_ty_at d D (nat_graph_ty f x y).
Proof.
  intros Hx Hy.
  cbn [nat_graph_ty precise_ty over_ty under_ty wf_context_ty_at
    q_nat_graph qual_vars qual_lvars erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [j|z] Hz; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

Lemma nat_singleton_bind_lookup x n (m : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (CtxBind x (nat_singleton_ty n)) ->
  forall s, (m : WorldT) s -> s !! x = Some (vnat n).
Proof.
  intros Hctx s Hs. rewrite ctx_denote_closed_bind in Hctx by apply nat_singleton_fv.
  apply res_models_and_iff in Hctx as [_ Hden].
  change (m ⊨ ty_denote_gas 2 (atom_env_to_lty_env {[x := TBase TNat]})
    (const_precise_ty (cnat n)) (tret (vfvar x))) in Hden.
  apply res_models_and_iff in Hden as [_ Hden].
  apply res_models_and_iff in Hden as [Hover _].
  eapply (ty_denote_over_ret_fvar_const_lookup 0 _ x (cnat n) m s);
    [apply atom_store_to_lvar_store_closed|exact Hover|exact Hs].
Qed.

Lemma const_over_open_lookup c r (m : WfWorldT) :
  m ⊨ over_open_body (base_ty_of_const c)
    (mk_q_eq (vbvar 0) (vconst c)) r ->
  forall s, (m : WorldT) s -> s !! r = Some (vconst c).
Proof.
  intros H s Hs. unfold over_open_body in H.
  rewrite typed_result_qual_const_eq, !const_qual_open_eq in H.
  replace (qual_vars (mk_q_eq (vfvar r) (vconst c)) ∖ {[LVFree r]})
    with (∅ : lvset) in H by (rewrite const_qual_open_vars; set_solver).
  apply res_models_fibvars_empty_elim in H.
  pose proof (res_models_over_FAtom_store_holds m _ H s Hs) as Hholds.
  cbn [qualifier_holds_store mk_q_eq qual_lvars lvar_value_keys
    denote_lvar_value] in Hholds.
  destruct Hholds as [Hlc [Hsub Hholds]].
  unfold lstore_on_lift_store in Hholds. cbn [lso_store storeAO_store] in Hholds.
  apply storeA_restrict_lookup_some in Hholds as [_ Hholds].
  rewrite lstore_lift_free_lookup_free in Hholds. exact Hholds.
Qed.

Lemma relevant_const_base_subset Σ c τ e :
  dom (relevant_env Σ (CTOver (base_ty_of_const c)
    (mk_q_eq (vbvar 0) (vconst c))) e) ⊆
  dom (relevant_env Σ τ e).
Proof.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  rewrite !storeA_restrict_dom.
  cbn [context_ty_lvars context_ty_lvars_at mk_q_eq qual_vars qual_lvars
    lvar_value_keys].
  rewrite lvars_at_depth_union, lvars_at_depth_singleton_bound0_succ,
    lvars_at_depth_empty. set_solver.
Qed.

Lemma nat_graph_refine_singleton Γ f x y n k :
  wf_ctx_under ∅ Γ ->
  x ∈ dom (erase_ctx Γ) -> y ∈ dom (erase_ctx Γ) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    (forall s, (m : WorldT) s -> s !! x = Some (vnat n)) /\
    (forall s, (m : WorldT) s -> s !! y = Some (vnat k))) ->
  sub_type_under ∅ Γ (nat_singleton_ty (f n k)) (nat_graph_ty f x y).
Proof.
  intros HΓ Hx Hy Hlookups.
  apply sub_type_under_intro; try assumption;
    [apply nat_singleton_wf|apply nat_graph_wf; assumption|reflexivity|].
  intros e m He Hctx Hden.
  destruct (Hlookups m Hctx) as [Hlookx Hlooky].
  pose proof (ty_denote_under_total ∅ Γ _ e m Hden) as Htotal.
  assert (Hwf : context_typing_wf ∅ Γ e (nat_graph_ty f x y)).
  { split; [exact HΓ|]. split; [apply nat_graph_wf; assumption|exact He]. }
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (nat_graph_ty f x y) e).
  { apply ty_denote_gas_zero_of_guard_formula.
    eapply ty_guard_relevant_of_static_full_total; [|exact Htotal].
    eapply context_typing_wf_denot_static_guard_full; eauto. }
  assert (Hover : m ⊨ ty_denote_gas 1 (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TNat (mk_q_eq (vbvar 0) (vnat (f n k)))) e).
  { unfold ty_denote_under, ty_denote in Hden.
    change (m ⊨ ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ))
      (const_precise_ty (cnat (f n k))) e) in Hden.
    apply res_models_and_iff in Hden as [_ Hden].
    apply res_models_and_iff in Hden as [H _]. exact H. }
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ))
    (nat_graph_ty f x y) e).
  apply res_models_and_iff. split.
  - eapply ty_denote_gas_guard_formula; exact Hzero.
  - apply res_models_and_iff. split.
    all: first [eapply (base_refinement_intro true 1
      (atom_env_to_lty_env (erase_ctx Γ)) TNat
      (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)) e m
      (world_dom (m : WorldT) ∪ dom (erase_ctx Γ) ∪ fv_tm e ∪ {[x;y]}))|
      eapply (base_refinement_intro false 1
      (atom_env_to_lty_env (erase_ctx Γ)) TNat
      (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)) e m
      (world_dom (m : WorldT) ∪ dom (erase_ctx Γ) ∪ fv_tm e ∪ {[x;y]}))];
      [first [exact (ty_denote_gas_zero_inter_l _ _ _ _ _ Hzero)|
        exact (ty_denote_gas_zero_inter_r _ _ _ _ _ Hzero)]|].
    all: intros r my Hr Hiny Hdom Hrestrict Hres.
    all: assert (HrΣ : r ∉ lvars_fv (dom (atom_env_to_lty_env (erase_ctx Γ))))
      by (rewrite lvars_fv_atom_env_to_lty_env_dom; clear -Hr; set_solver).
    all: assert (HrSmall : r ∉ lvars_fv (dom (relevant_env
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TNat (mk_q_eq (vbvar 0) (vnat (f n k)))) e))) by
      (intros Hin; apply HrΣ; apply lvars_fv_elem;
       apply (relevant_env_dom_subset_direct (atom_env_to_lty_env (erase_ctx Γ))
         (CTOver TNat (mk_q_eq (vbvar 0) (vnat (f n k)))) e);
       apply lvars_fv_elem; exact Hin).
    all: assert (HrBig : LVFree r ∉ dom (relevant_env
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) e)) by
      (intros Hin; apply HrΣ; apply lvars_fv_elem;
       apply (relevant_env_dom_subset_direct (atom_env_to_lty_env (erase_ctx Γ))
         (CTOver TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) e); exact Hin).
    all: assert (HresSmall : my ⊨ expr_result_formula_at
      (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTOver TNat (mk_q_eq (vbvar 0) (vnat (f n k)))) e)) e (LVFree r)) by
      (eapply (expr_result_formula_at_coarsen_domain
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTOver TNat (mk_q_eq (vbvar 0) (vnat (f n k)))) e))
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTOver TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) e))
        e r my);
       [apply (relevant_const_base_subset _ (cnat (f n k)))|
        exact (ty_denote_gas_tm_lvars_relevant_env_dom _ _ _ _ _ Hover)|
        exact HrBig|exact Hres]).
    all: assert (Hout : my ⊨ over_open_body TNat
      (mk_q_eq (vbvar 0) (vnat (f n k))) r).
    all: try (eapply (ty_denote_gas_over_result_body_elim 0
      (atom_env_to_lty_env (erase_ctx Γ)) TNat
      (mk_q_eq (vbvar 0) (vnat (f n k))) e r m my);
      [apply atom_store_to_lvar_store_closed|
       eapply context_typing_wf_lc_tm; exact Hwf|
       clear -Hr; set_solver|clear -Hr; set_solver|exact HrSmall|
       apply const_qual_dom_bound_fresh|exact Hdom|exact Hrestrict|
       exact HresSmall|exact Hover]).
    all: eapply nat_graph_exact_open_body;
      [clear -Hr; set_solver|
       eapply lookup_from_extension; [exact Hrestrict|exact Hlookx]|
       eapply lookup_from_extension; [exact Hrestrict|exact Hlooky]|
       exact (const_over_open_lookup (cnat (f n k)) r my Hout)].
Qed.

Lemma nat_graph_relevant pol Σ f x y e :
  LVFree x ∈ dom Σ -> LVFree y ∈ dom Σ -> tm_lvars e ⊆ dom Σ ->
  tm_lvars e ⊆ dom (relevant_env Σ
    (polarity_ty pol TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) e) /\
  ({[x;y]} : aset) ⊆ lvars_fv (dom (relevant_env Σ
    (polarity_ty pol TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) e)).
Proof.
  intros Hx Hy He.
  assert (Hcty : context_ty_lvars
    (polarity_ty pol TNat (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0))) =
    ({[LVFree x;LVFree y]} : lvset)).
  { destruct pol; cbn [polarity_ty context_ty_lvars context_ty_lvars_at
      q_nat_graph qual_vars qual_lvars];
      rewrite !lvars_at_depth_union, !lvars_at_depth_singleton_free,
        !lvars_at_depth_singleton_bound0_succ; set_solver. }
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  rewrite !storeA_restrict_dom, Hcty. split; [set_solver|].
  intros z Hz. apply lvars_fv_elem. clear -Hx Hy Hz.
  assert (Hz' : LVFree z ∈ ({[LVFree x;LVFree y]} : lvset)) by set_solver.
  set_solver.
Qed.

Lemma nat_graph_joinable Γ f x y e :
  context_typing_wf ∅ Γ e (nat_graph_ty f x y) ->
  x ∈ dom (erase_ctx Γ) -> y ∈ dom (erase_ctx Γ) ->
  fiberwise_joinable_on {[x;y]}
    (ty_denote_under ∅ Γ (nat_graph_ty f x y) e).
Proof.
  intros Hwf Hx Hy.
  pose proof (context_typing_wf_basic_typing _ _ _ _ Hwf) as He.
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf) as Hlce.
  pose proof (basic_tm_has_ltype_lvars _ _ _
    (basic_tm_has_ltype_of_atom_env_typing _ _ _ He)) as Hvars.
  assert (HeΣ : tm_lvars e ⊆ dom (atom_env_to_lty_env (erase_ctx Γ))).
  { rewrite tm_lvars_lc_eq_atoms by exact Hlce. exact Hvars. }
  assert (HxΣ : LVFree x ∈ dom (atom_env_to_lty_env (erase_ctx Γ))).
  { apply lvars_fv_elem. rewrite lvars_fv_atom_env_to_lty_env_dom. exact Hx. }
  assert (HyΣ : LVFree y ∈ dom (atom_env_to_lty_env (erase_ctx Γ))).
  { apply lvars_fv_elem. rewrite lvars_fv_atom_env_to_lty_env_dom. exact Hy. }
  destruct (nat_graph_relevant true _ f x y e HxΣ HyΣ HeΣ) as [HeOver HXOver].
  destruct (nat_graph_relevant false _ f x y e HxΣ HyΣ HeΣ) as [HeUnder HXUnder].
  unfold ty_denote_under, ty_denote.
  change (fiberwise_joinable_on {[x;y]}
    (ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ)) (nat_graph_ty f x y) e)).
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_ty_guard_formula.
  - apply fiberwise_joinable_on_and.
    + eapply (fiberwise_joinable_on_ty_denote_gas_over {[x;y]} 1
        (atom_env_to_lty_env (erase_ctx Γ)) TNat
        (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)) e);
        [apply atom_store_to_lvar_store_closed|exact Hlce|exact HeOver|exact HXOver].
    + eapply (fiberwise_joinable_on_ty_denote_gas_under {[x;y]} 1
        (atom_env_to_lty_env (erase_ctx Γ)) TNat
        (q_nat_graph f (LVFree x) (LVFree y) (LVBound 0)) e);
        [apply atom_store_to_lvar_store_closed|exact Hlce|exact HeUnder|exact HXUnder].
Qed.

Lemma typing_closed_weaken Φ Γ e τ :
  wf_ctx_under ∅ Γ ->
  has_context_type Φ ∅ CtxEmpty e τ ->
  has_context_type Φ ∅ Γ e τ.
Proof.
  intros HΓ Hty.
  pose proof (typing_wf_under _ _ _ _ _ Hty) as Hwf.
  pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf) as HeFV.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf) as HτFV.
  assert (Hwf' : context_typing_wf ∅ Γ e τ).
  { split; [exact HΓ|]. split.
    - eapply wf_context_ty_at_mono_env; [|exact (proj1 (proj2 Hwf))]. set_solver.
    - eapply basic_typing_weaken_tm; [exact (proj2 (proj2 Hwf))|]. apply map_empty_subseteq. }
  eapply CT_CtxSub; [exact Hwf'|exact Hty|].
  split; [exact HΓ|]. split; [constructor|]. split.
  - intros z Hz. cbn [erase_ctx] in HeFV, HτFV. set_solver.
  - intros m _. exists m. split; [apply res_restrict_le|].
    cbn [ctx_denote_under ctx_fv erase_ctx]. rewrite storeA_restrict_empty_set.
    apply res_models_and_iff. split; [apply basic_world_formula_empty|apply res_models_true].
Qed.

Lemma nat_pair_lookups x y τx τy :
  x <> y -> erase_ty τx = TBase TNat -> erase_ty τy = TBase TNat ->
  erase_ctx (nat_pair_ctx x y τx τy) !! x = Some (TBase TNat) /\
  erase_ctx (nat_pair_ctx x y τx τy) !! y = Some (TBase TNat).
Proof.
  intros Hxy Hx Hy.
  cbn [nat_pair_ctx erase_ctx]. rewrite Hx, Hy.
  unfold store_union, store_empty. rewrite map_empty_union.
  split.
  - apply map_lookup_union_Some_raw. left. apply lookup_singleton_eq.
  - apply map_lookup_union_Some_raw. right. split.
    + apply lookup_singleton_ne. congruence.
    + apply lookup_singleton_eq.
Qed.

Lemma typing_nat_pair_cases Φ f x y e :
  x <> y ->
  context_typing_wf ∅ (nat_pair_ctx x y nat_over_ty nat_over_ty) e
    (nat_graph_ty f x y) ->
  (forall n k, has_context_type Φ ∅
    (nat_pair_ctx x y (nat_singleton_ty n) (nat_singleton_ty k)) e
    (nat_graph_ty f x y)) ->
  has_context_type Φ ∅ (nat_pair_ctx x y nat_over_ty nat_over_ty) e
    (nat_graph_ty f x y).
Proof.
  intros Hxy Hwf Hcases.
  destruct (nat_pair_lookups x y nat_over_ty nat_over_ty Hxy eq_refl eq_refl)
    as [Hx Hy].
  eapply CT_FiberCases with (I := (nat * nat)%type) (X := {[x;y]})
    (cases := fun p => nat_pair_ctx x y (nat_singleton_ty p.1) (nat_singleton_ty p.2)).
  - exact Hwf.
  - intros [n k]. reflexivity.
  - intros [n k]. apply Hcases.
  - apply nat_graph_joinable; [exact Hwf|apply elem_of_dom; eauto|apply elem_of_dom; eauto].
  - intros m Hctx σ mfib Hfib.
    destruct (nat_pair_fiber_constants x y σ m mfib Hctx Hfib) as [n [k Hnk]].
    exists (n,k). exact Hnk.
Qed.


Lemma arithmetic_body_closed_basic is_add n k :
  tm_has_type ∅ (arithmetic_body is_add (vnat n) (vnat k)) (TBase TNat).
Proof. destruct is_add; type_arith. Qed.

Lemma arithmetic_body_closed_typing Φ is_add n k :
  has_context_type Φ ∅ CtxEmpty
    (arithmetic_body is_add (vnat n) (vnat k))
    (nat_singleton_ty (arithmetic_function is_add n k)).
Proof.
  assert (Hinstance : has_context_type Φ ∅ CtxEmpty
    (NatArithmetic.app2 (arithmetic_value is_add) (vnat n) (vnat k))
    (nat_singleton_ty (arithmetic_function is_add n k))).
  { destruct is_add; [apply add_instance_typing|apply sub_instance_typing]. }
  pose proof (arithmetic_prefix_equivalence _ _
    (arithmetic_body_prefix is_add n k)) as [Hrun Htotal].
  pose proof (typing_wf_under _ _ _ _ _ Hinstance) as Hwf.
  assert (Hsource : fv_tm
    (NatArithmetic.app2 (arithmetic_value is_add) (vnat n) (vnat k)) = ∅).
  { eapply basic_typing_closed_tm. exact (proj2 (proj2 Hwf)). }
  assert (Htarget : fv_tm (arithmetic_body is_add (vnat n) (vnat k)) = ∅).
  { eapply basic_typing_closed_tm. apply arithmetic_body_closed_basic. }
  eapply CT_Conv; [|exact Hinstance|].
  - split; [constructor|]. split; [apply nat_singleton_wf|apply arithmetic_body_closed_basic].
  - intros m _. split.
    + intros s v _. unfold tm_eval_in_store, expr_eval_in_store.
      rewrite !instantiate_closed_tm by assumption. apply Hrun.
    + intros s _. rewrite !instantiate_closed_tm by assumption. exact Htotal.
Qed.

Lemma nat_pair_singleton_lookups x y n k m :
  m ⊨ ctx_denote_under ∅
    (nat_pair_ctx x y (nat_singleton_ty n) (nat_singleton_ty k)) ->
  (forall s, (m : WorldT) s -> s !! x = Some (vnat n)) /\
  (forall s, (m : WorldT) s -> s !! y = Some (vnat k)).
Proof.
  intros Hctx.
  destruct (nat_pair_denote_inv ∅ x y _ _ m
    (nat_singleton_fv n) (nat_singleton_fv k) Hctx) as [Hx Hy].
  split; eapply nat_singleton_bind_lookup; eauto.
Qed.

Lemma arithmetic_body_pair_wf is_add x y τx τy τ :
  x <> y -> basic_context_ty ∅ τx -> basic_context_ty ∅ τy ->
  erase_ty τx = TBase TNat -> erase_ty τy = TBase TNat ->
  erase_ty τ = TBase TNat ->
  wf_context_ty_at 0 (dom (erase_ctx (nat_pair_ctx x y τx τy))) τ ->
  context_typing_wf ∅ (nat_pair_ctx x y τx τy)
    (arithmetic_body is_add (vfvar x) (vfvar y)) τ.
Proof.
  intros Hxy Hτx Hτy Hex Hey He Hτ.
  split; [apply nat_pair_ctx_wf; assumption|]. split; [exact Hτ|].
  rewrite He. apply arithmetic_body_typed;
    destruct (nat_pair_lookups x y τx τy Hxy Hex Hey); assumption.
Qed.

Lemma arithmetic_body_exact_typing Φ is_add x y n k :
  x <> y ->
  has_context_type Φ ∅
    (nat_pair_ctx x y (nat_singleton_ty n) (nat_singleton_ty k))
    (arithmetic_body is_add (vfvar x) (vfvar y))
    (nat_graph_ty (arithmetic_function is_add) x y).
Proof.
  intros Hxy.
  set (Γ := nat_pair_ctx x y (nat_singleton_ty n) (nat_singleton_ty k)).
  assert (HΓ : wf_ctx_under ∅ Γ).
  { apply nat_pair_ctx_wf; [exact Hxy|apply nat_singleton_wf|apply nat_singleton_wf]. }
  destruct (nat_pair_lookups x y (nat_singleton_ty n) (nat_singleton_ty k) Hxy eq_refl eq_refl) as [Hx Hy].
  assert (Hxdom : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hydom : y ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hwf : context_typing_wf ∅ Γ
    (arithmetic_body is_add (vfvar x) (vfvar y))
    (nat_graph_ty (arithmetic_function is_add) x y)).
  { apply arithmetic_body_pair_wf; try reflexivity;
      [exact Hxy|apply nat_singleton_wf|apply nat_singleton_wf|].
    apply nat_graph_wf; assumption. }
  eapply CT_Sub; [exact Hwf| |].
  - eapply CT_Conv.
    + split; [exact HΓ|]. split; [apply nat_singleton_wf|exact (proj2 (proj2 Hwf))].
    + apply typing_closed_weaken; [exact HΓ|apply arithmetic_body_closed_typing].
    + intros m Hctx.
      destruct (nat_pair_singleton_lookups x y n k m Hctx) as [Hsx Hsy].
      assert (Hclosed : fv_tm (arithmetic_body is_add (vnat n) (vnat k)) = ∅).
      { eapply basic_typing_closed_tm. apply arithmetic_body_closed_basic. }
      split.
      * intros s v Hs. unfold tm_eval_in_store, expr_eval_in_store.
        rewrite instantiate_closed_tm by exact Hclosed.
        rewrite (arithmetic_body_instantiate is_add s x y n k (Hsx s Hs) (Hsy s Hs)).
        reflexivity.
      * intros s Hs. rewrite instantiate_closed_tm by exact Hclosed.
        rewrite (arithmetic_body_instantiate is_add s x y n k (Hsx s Hs) (Hsy s Hs)).
        reflexivity.
  - apply nat_graph_refine_singleton; try assumption.
    intros m Hctx. exact (nat_pair_singleton_lookups x y n k m Hctx).
Qed.

Lemma arithmetic_body_typing Φ is_add x y :
  x <> y ->
  has_context_type Φ ∅ (nat_pair_ctx x y nat_over_ty nat_over_ty)
    (arithmetic_body is_add (vfvar x) (vfvar y))
    (nat_graph_ty (arithmetic_function is_add) x y).
Proof.
  intros Hxy. apply typing_nat_pair_cases; [exact Hxy| |].
  - apply arithmetic_body_pair_wf; try reflexivity;
      [exact Hxy|apply nat_over_wf|apply nat_over_wf|].
    apply nat_graph_wf;
      destruct (nat_pair_lookups x y nat_over_ty nat_over_ty Hxy eq_refl eq_refl)
        as [Hx Hy]; apply elem_of_dom; eauto.
  - intros n k. apply arithmetic_body_exact_typing. exact Hxy.
Qed.

Definition nat_inner_ty f x :=
  CTArrow nat_over_ty
    (precise_ty TNat (q_nat_graph f (LVFree x) (LVBound 1) (LVBound 0))).
Definition nat_function_ty f :=
  CTArrow nat_over_ty
    (CTArrow nat_over_ty
      (precise_ty TNat (q_nat_graph f (LVBound 2) (LVBound 1) (LVBound 0)))).

Lemma nat_function_spec f : nat_binop_context_ty f = CTPersist (nat_function_ty f).
Proof. reflexivity. Qed.

Lemma nat_function_open f x :
  cty_open 0 x
    (CTArrow nat_over_ty
      (precise_ty TNat (q_nat_graph f (LVBound 2) (LVBound 1) (LVBound 0)))) =
  nat_inner_ty f x.
Proof.
  cbn [cty_open nat_over_ty over_ty under_ty precise_ty nat_inner_ty].
  rewrite !q_nat_graph_open, qual_open_atom_top_on.
  rewrite set_swap_singleton.
  base_swap_normalize. reflexivity.
Qed.

Lemma nat_inner_open f x y : x <> y ->
  cty_open 0 y
    (precise_ty TNat (q_nat_graph f (LVFree x) (LVBound 1) (LVBound 0))) =
  nat_graph_ty f x y.
Proof.
  intros Hxy. cbn [cty_open precise_ty over_ty under_ty nat_graph_ty].
  rewrite !q_nat_graph_open. base_swap_normalize. reflexivity.
Qed.

Definition nat_one_ctx x := CtxComma CtxEmpty (CtxBind x nat_over_ty).

Lemma nat_one_erasure x : erase_ctx (nat_one_ctx x) = {[x := TBase TNat]}.
Proof. cbn [nat_one_ctx erase_ctx]. unfold store_union, store_empty. apply map_empty_union. Qed.

Lemma nat_one_wf x : wf_ctx_under ∅ (nat_one_ctx x).
Proof.
  cbn [wf_ctx_under nat_one_ctx basic_ctx ctx_dom].
  repeat split; try set_solver.
Qed.

Lemma nat_one_lookup x m :
  m ⊨ ctx_denote_under ∅ (nat_one_ctx x) ->
  forall s, (m : WorldT) s -> exists n, s !! x = Some (vnat n).
Proof.
  intros Hctx s Hs. unfold nat_one_ctx in Hctx.
  apply res_models_and_iff in Hctx as [_ Hctx].
  apply res_models_and_iff in Hctx as [_ Hctx].
  cbn [ctx_fv erase_ctx] in Hctx.
  rewrite nat_over_fv, !storeA_restrict_empty_set in Hctx.
  unfold store_union, store_empty in Hctx. rewrite !map_empty_union in Hctx.
  apply res_models_and_iff in Hctx as [_ Hden].
  destruct (ty_denote_ret_fvar_base_const 1
    (atom_env_to_lty_env ({[x := TBase TNat]})) nat_over_ty TNat x m
    eq_refl Hden s Hs) as [c [Hx Hc]].
  destruct c as [|b|n|tr|xs|z]; cbn [base_ty_of_const] in Hc; try discriminate.
  exists n. exact Hx.
Qed.

Lemma nat_inner_wf d D f x : x ∈ D ->
  wf_context_ty_at d D (nat_inner_ty f x).
Proof.
  intros Hx. cbn [nat_inner_ty precise_ty over_ty under_ty wf_context_ty_at].
  split; [apply nat_over_wf|].
  cbn [q_nat_graph qual_vars qual_lvars erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [j|z] Hz; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

Lemma arithmetic_call_basic is_add Δ x :
  Δ !! x = Some (TBase TNat) ->
  tm_has_type Δ (tapp_tm (tret (arithmetic_value is_add)) (vfvar x)) (TNat →ᵦ TNat).
Proof.
  intros Hx. assert (Hxdom : x ∈ dom Δ) by (apply elem_of_dom; eauto).
  destruct is_add; type_arith.
Qed.

Lemma arithmetic_partial_typing Φ is_add x :
  has_context_type Φ ∅ (nat_one_ctx x)
    (tret (arithmetic_partial is_add (vfvar x)))
    (nat_inner_ty (arithmetic_function is_add) x).
Proof.
  rewrite arithmetic_partial_lam. unfold nat_inner_ty.
  eapply CT_Lam with (τx := nat_over_ty) (L := {[x]}).
  - split; [apply nat_one_wf|]. split.
    + apply nat_inner_wf. apply elem_of_dom. exists (TBase TNat).
      rewrite nat_one_erasure. apply lookup_singleton_eq.
    + apply TT_Ret. rewrite <- arithmetic_partial_lam.
      apply arithmetic_partial_typed. rewrite nat_one_erasure. apply lookup_singleton_eq.
  - intros y Hy. rewrite nat_inner_open.
    2: { intros Heq. subst y. apply Hy. apply elem_of_singleton. reflexivity. }
    change (has_context_type Φ ∅ (nat_pair_ctx x y nat_over_ty nat_over_ty)
      (open_tm 0 (vfvar y) (arithmetic_lam_body is_add (vfvar x)))
      (nat_graph_ty (arithmetic_function is_add) x y)).
    rewrite <- arithmetic_body_open.
    apply arithmetic_body_typing. intros Heq. subst y. apply Hy. apply elem_of_singleton. reflexivity.
Qed.

Lemma arithmetic_first_call_typing Φ is_add x :
  has_context_type Φ ∅ (nat_one_ctx x)
    (tapp_tm (tret (arithmetic_value is_add)) (vfvar x))
    (nat_inner_ty (arithmetic_function is_add) x).
Proof.
  eapply CT_Conv; [|apply arithmetic_partial_typing|].
  - split; [apply nat_one_wf|]. split.
    + apply nat_inner_wf. apply elem_of_dom. exists (TBase TNat).
      rewrite nat_one_erasure. apply lookup_singleton_eq.
    + apply arithmetic_call_basic. rewrite nat_one_erasure. apply lookup_singleton_eq.
  - intros m Hctx. split.
    + intros s v Hs.
      destruct (nat_one_lookup x m Hctx s Hs) as [n Hn].
      unfold tm_eval_in_store, expr_eval_in_store.
      rewrite (arithmetic_partial_instantiate is_add s x n Hn),
        (arithmetic_call_instantiate is_add s x n Hn).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _
        (arithmetic_partial_prefix is_add n)) v).
    + intros s Hs.
      destruct (nat_one_lookup x m Hctx s Hs) as [n Hn].
      rewrite (arithmetic_partial_instantiate is_add s x n Hn),
        (arithmetic_call_instantiate is_add s x n Hn).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _
        (arithmetic_partial_prefix is_add n))).
Qed.

Lemma empty_context_persistent : persistent_formula (ctx_denote_under ∅ CtxEmpty).
Proof.
  apply persistent_formula_of_singleton_projection.
  intros m Hm. exists (∅ : gmap atom value).
  assert (Hfv : formula_fv (ctx_denote_under ∅ CtxEmpty) = ∅).
  { cbn [ctx_denote_under erase_ctx ctx_fv].
    rewrite formula_fv_and, formula_fv_basic_world_formula, (formula_fv_true (V := value)).
    unfold store_union, store_empty. rewrite ?map_empty_union.
    rewrite lvars_fv_atom_env_to_lty_env_dom, ?dom_empty_L. set_solver. }
  rewrite Hfv. split; [reflexivity|].
  apply wfworld_ext. apply world_ext.
  - cbn [world_dom raw_world res_restrict resA_restrict raw_worldA rawA_restrict
      singleton_world singleton_worldA worldA_dom]. set_solver.
  - intros s. split.
    + intros [s0 [Hs0 Heq]]. rewrite storeA_restrict_empty_set in Heq.
      exact (eq_sym Heq).
    + intros ->. destruct (world_wf m) as [[s Hs] _].
      exists s. split; [exact Hs|apply storeA_restrict_empty_set].
Qed.

Theorem arithmetic_value_context_typed Φ is_add :
  has_context_type Φ ∅ CtxEmpty (tret (arithmetic_value is_add))
    (nat_binop_context_ty (arithmetic_function is_add)).
Proof.
  rewrite nat_function_spec. apply CT_PersistIntro.
  - split; [constructor|]. split.
    + exact (nat_binop_context_ty_well_formed (arithmetic_function is_add)).
    + apply TT_Ret. apply arithmetic_value_typed.
  - apply empty_context_persistent.
  - unfold nat_function_ty. eapply CT_ArrowIntro with (L := ∅).
    + split; [constructor|]. split.
      * exact (nat_binop_context_ty_well_formed (arithmetic_function is_add)).
      * apply TT_Ret. apply arithmetic_value_typed.
    + intros x _. rewrite nat_function_open. apply arithmetic_first_call_typing.
Qed.

(** Genuine [has_context_type] derivations for the original library specs. *)
Theorem add_value_context_typed Φ :
  has_context_type Φ ∅ CtxEmpty (tret NatArithmetic.add_value) add_context_ty.
Proof. exact (arithmetic_value_context_typed Φ true). Qed.

Theorem sub_value_context_typed Φ :
  has_context_type Φ ∅ CtxEmpty (tret NatArithmetic.sub_value) sub_context_ty.
Proof. exact (arithmetic_value_context_typed Φ false). Qed.
