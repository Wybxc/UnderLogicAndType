(** Exact list-valued graphs and their fiberwise typing support. *)
From CaseStudy Require Export MergeProgram NatArithmeticTyping.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From Denotation Require Import Context ConstDenote ConstDenoteBase TypeEquiv TypeEquivCore
  TypeEquivTermBase TypeEquivBody TypeEquivFiberBaseCore BaseIntro.
From ContextTyping Require Import Typing TypingRegular NatCases Conversion Subtyping SoundnessLam
  SoundnessVar Soundness ConstCases OverConsequence FiberSupport.
From Denotation Require Import OverConsequence.
From Stdlib Require Import List Lia.
Import ListNotations.
Definition merge_singleton_ty xs := const_precise_ty (clist xs).
Lemma merge_singleton_wf d D xs : wf_context_ty_at d D (merge_singleton_ty xs).
Proof. apply const_precise_wf. Qed.
Definition q_merge_graph (f : list nat -> list nat -> list nat) (u v w : logic_var) : type_qualifier :=
  tqual ({[u]} ∪ {[v]} ∪ {[w]})
    (fun s => exists n k,
      lso_store s !! u = Some (IncorrectMerge.vlist n) /\
      lso_store s !! v = Some (IncorrectMerge.vlist k) /\
      lso_store s !! w = Some (IncorrectMerge.vlist (f n k))).

Lemma q_merge_graph_open f u v w j z :
  qual_open_atom j z (q_merge_graph f u v w) =
  q_merge_graph f (swap (LVBound j) (LVFree z) u)
    (swap (LVBound j) (LVFree z) v) (swap (LVBound j) (LVFree z) w).
Proof.
  apply qual_ext.
  - cbn [qual_open_atom q_merge_graph qual_lvars].
    rewrite !set_swap_union, !set_swap_singleton. reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_open_atom q_merge_graph qual_prop qual_lvars].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value.
    setoid_rewrite Hs. reflexivity.
Qed.

Lemma q_merge_graph_typed f u v :
  typed_result_qual TList (q_merge_graph f u v (LVBound 0)) =
  q_merge_graph f u v (LVBound 0).
Proof.
  apply qual_ext.
  - cbn [typed_result_qual q_merge_graph qual_lvars qual_vars]. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [typed_result_qual q_merge_graph qual_prop qual_lvars qual_vars].
    unfold lstore_on_restrict, storeA_on_restrict.
    cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by set_solver.
    setoid_rewrite Hs.
    split; [tauto|]. intros [n [k [Hu [Hv Hw]]]].
    split.
    + exists n,k. auto.
    + exists (IncorrectMerge.vlist (f n k)). split; [exact Hw|constructor].
Qed.

Lemma q_merge_graph_subst f x y r σ n k :
  σ !! x = Some (IncorrectMerge.vlist n) -> σ !! y = Some (IncorrectMerge.vlist k) ->
  dom (σ : gmap atom value) = {[x;y]} -> r ∉ ({[x;y]} : aset) ->
  qual_msubst_store σ (q_merge_graph f (LVFree x) (LVFree y) (LVFree r)) =
  mk_q_eq (vfvar r) (IncorrectMerge.vlist (f n k)).
Proof.
  intros Hx Hy Hdom Hr.
  apply qual_ext.
  - cbn [qual_msubst_store qual_mlsubst q_merge_graph mk_q_eq qual_lvars
      lvar_value_keys].
    rewrite atom_store_to_lvar_store_dom, Hdom.
    unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver.
  - intros [ss1 Hd1] [ss2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [qual_msubst_store qual_mlsubst q_merge_graph mk_q_eq qual_prop
      qual_lvars lvar_value_keys denote_lvar_value].
    unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    set (D := ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]} : lvset)).
    assert (Hsx : (ss1 : gmap logic_var value) !! LVFree x = None).
    { apply not_elem_of_dom. rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_merge_graph qual_lvars].
      rewrite atom_store_to_lvar_store_dom, Hdom.
      unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver. }
    assert (Hsy : (ss1 : gmap logic_var value) !! LVFree y = None).
    { apply not_elem_of_dom. rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_merge_graph qual_lvars].
      rewrite atom_store_to_lvar_store_dom, Hdom.
      unfold lvars_of_atoms. rewrite !set_map_union_L, !set_map_singleton_L. set_solver. }
    assert (Hsr : LVFree r ∈ dom (ss1 : gmap logic_var value)).
    { rewrite Hd1.
      cbn [qual_msubst_store qual_mlsubst q_merge_graph qual_lvars].
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


Lemma merge_graph_exact_open_body pol f x y r n k (m : WfWorldT) :
  r ∉ ({[x;y]} : aset) ->
  (forall s, (m : WorldT) s -> s !! x = Some (IncorrectMerge.vlist n)) ->
  (forall s, (m : WorldT) s -> s !! y = Some (IncorrectMerge.vlist k)) ->
  (forall s, (m : WorldT) s -> s !! r = Some (IncorrectMerge.vlist (f n k))) ->
  m ⊨ polarity_open_body pol TList
    (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)) r.
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
    rewrite q_merge_graph_typed, !q_merge_graph_open;
    base_swap_normalize;
    replace (qual_vars (q_merge_graph f (LVFree x) (LVFree y) (LVFree r)) ∖
      {[LVFree r]}) with ({[LVFree x;LVFree y]} : lvset)
      by (cbn [q_merge_graph qual_vars qual_lvars]; set_solver);
    eapply res_models_FFibVars_intro.
  1,4: unfold formula_scoped_in_world;
    rewrite formula_fv_fibvars;
    first [rewrite formula_fv_over|rewrite formula_fv_under];
    rewrite formula_fv_atom;
    cbn [qual_dom qual_vars q_merge_graph qual_lvars];
    rewrite !lvars_fv_union, !lvars_fv_singleton_free; clear -Hdomxy Hdomr; set_solver.
  1,3: intros [j|z] Hz; cbn [lc_logic_var_key]; [set_solver|exact I].
  all: intros σ mfib Hfib;
    rewrite !lvars_fv_union, !lvars_fv_singleton_free in Hfib;
    assert (Hdomσ : dom (σ : gmap atom value) = {[x;y]}) by
      (pose proof (wfworld_store_dom (res_restrict m {[x;y]}) σ (proj1 Hfib)) as H;
       cbn in H; rewrite H; set_solver);
    assert (Hσx : σ !! x = Some (IncorrectMerge.vlist n)) by
      (eapply (lookup_in_projection m mfib {[x;y]} σ x (IncorrectMerge.vlist n));
       [set_solver|exact Hfib|exact Hx]);
    assert (Hσy : σ !! y = Some (IncorrectMerge.vlist k)) by
      (eapply (lookup_in_projection m mfib {[x;y]} σ y (IncorrectMerge.vlist k));
       [set_solver|exact Hfib|exact Hy]);
    first [change (mfib ⊨ FOver (FAtom (qual_msubst_store σ
      (q_merge_graph f (LVFree x) (LVFree y) (LVFree r))))) |
      change (mfib ⊨ FUnder (FAtom (qual_msubst_store σ
      (q_merge_graph f (LVFree x) (LVFree y) (LVFree r)))))];
    rewrite (q_merge_graph_subst f x y r σ n k Hσx Hσy Hdomσ Hr);
    first [apply res_models_over_intro_same_from_model|
      apply res_models_under_intro_same_from_model];
    apply const_type_qualifier_open_from_lookup;
    intros s Hs; apply Hlookr;
    eapply res_fiber_from_projection_store_source; eauto.
Qed.

Definition merge_graph_ty f x y :=
  precise_ty TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)).

Lemma merge_graph_wf d D f x y :
  x ∈ D -> y ∈ D -> wf_context_ty_at d D (merge_graph_ty f x y).
Proof.
  intros Hx Hy.
  cbn [merge_graph_ty precise_ty over_ty under_ty wf_context_ty_at
    q_merge_graph qual_vars qual_lvars erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [j|z] Hz; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.


Lemma merge_graph_refine_singleton Γ f x y n k :
  wf_ctx_under ∅ Γ ->
  x ∈ dom (erase_ctx Γ) -> y ∈ dom (erase_ctx Γ) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    (forall s, (m : WorldT) s -> s !! x = Some (IncorrectMerge.vlist n)) /\
    (forall s, (m : WorldT) s -> s !! y = Some (IncorrectMerge.vlist k))) ->
  sub_type_under ∅ Γ (merge_singleton_ty (f n k)) (merge_graph_ty f x y).
Proof.
  intros HΓ Hx Hy Hlookups.
  apply sub_type_under_intro; try assumption;
    [apply merge_singleton_wf|apply merge_graph_wf; assumption|reflexivity|].
  intros e m He Hctx Hden.
  destruct (Hlookups m Hctx) as [Hlookx Hlooky].
  pose proof (ty_denote_under_total ∅ Γ _ e m Hden) as Htotal.
  assert (Hwf : context_typing_wf ∅ Γ e (merge_graph_ty f x y)).
  { split; [exact HΓ|]. split; [apply merge_graph_wf; assumption|exact He]. }
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (merge_graph_ty f x y) e).
  { apply ty_denote_gas_zero_of_guard_formula.
    eapply ty_guard_relevant_of_static_full_total; [|exact Htotal].
    eapply context_typing_wf_denot_static_guard_full; eauto. }
  assert (Hover : m ⊨ ty_denote_gas 1 (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TList (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k)))) e).
  { unfold ty_denote_under, ty_denote in Hden.
    change (m ⊨ ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ))
      (const_precise_ty (clist (f n k))) e) in Hden.
    apply res_models_and_iff in Hden as [_ Hden].
    apply res_models_and_iff in Hden as [H _]. exact H. }
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ))
    (merge_graph_ty f x y) e).
  apply res_models_and_iff. split.
  - eapply ty_denote_gas_guard_formula; exact Hzero.
  - apply res_models_and_iff. split.
    all: first [eapply (base_refinement_intro true 1
      (atom_env_to_lty_env (erase_ctx Γ)) TList
      (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)) e m
      (world_dom (m : WorldT) ∪ dom (erase_ctx Γ) ∪ fv_tm e ∪ {[x;y]}))|
      eapply (base_refinement_intro false 1
      (atom_env_to_lty_env (erase_ctx Γ)) TList
      (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)) e m
      (world_dom (m : WorldT) ∪ dom (erase_ctx Γ) ∪ fv_tm e ∪ {[x;y]}))];
      [first [exact (ty_denote_gas_zero_inter_l _ _ _ _ _ Hzero)|
        exact (ty_denote_gas_zero_inter_r _ _ _ _ _ Hzero)]|].
    all: intros r my Hr Hiny Hdom Hrestrict Hres.
    all: assert (HrΣ : r ∉ lvars_fv (dom (atom_env_to_lty_env (erase_ctx Γ))))
      by (rewrite lvars_fv_atom_env_to_lty_env_dom; clear -Hr; set_solver).
    all: assert (HrSmall : r ∉ lvars_fv (dom (relevant_env
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TList (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k)))) e))) by
      (intros Hin; apply HrΣ; apply lvars_fv_elem;
       apply (relevant_env_dom_subset_direct (atom_env_to_lty_env (erase_ctx Γ))
         (CTOver TList (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k)))) e);
       apply lvars_fv_elem; exact Hin).
    all: assert (HrBig : LVFree r ∉ dom (relevant_env
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) e)) by
      (intros Hin; apply HrΣ; apply lvars_fv_elem;
       apply (relevant_env_dom_subset_direct (atom_env_to_lty_env (erase_ctx Γ))
         (CTOver TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) e); exact Hin).
    all: assert (HresSmall : my ⊨ expr_result_formula_at
      (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTOver TList (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k)))) e)) e (LVFree r)) by
      (eapply (expr_result_formula_at_coarsen_domain
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTOver TList (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k)))) e))
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTOver TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) e))
        e r my);
       [apply (relevant_const_base_subset _ (clist (f n k)))|
        exact (ty_denote_gas_tm_lvars_relevant_env_dom _ _ _ _ _ Hover)|
        exact HrBig|exact Hres]).
    all: assert (Hout : my ⊨ over_open_body TList
      (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k))) r).
    all: try (eapply (ty_denote_gas_over_result_body_elim 0
      (atom_env_to_lty_env (erase_ctx Γ)) TList
      (mk_q_eq (vbvar 0) (IncorrectMerge.vlist (f n k))) e r m my);
      [apply atom_store_to_lvar_store_closed|
       eapply context_typing_wf_lc_tm; exact Hwf|
       clear -Hr; set_solver|clear -Hr; set_solver|exact HrSmall|
       apply const_qual_dom_bound_fresh|exact Hdom|exact Hrestrict|
       exact HresSmall|exact Hover]).
    all: eapply merge_graph_exact_open_body;
      [clear -Hr; set_solver|
       eapply lookup_from_extension; [exact Hrestrict|exact Hlookx]|
       eapply lookup_from_extension; [exact Hrestrict|exact Hlooky]|
       exact (const_over_open_lookup (clist (f n k)) r my Hout)].
Qed.

Lemma merge_graph_relevant pol Σ f x y e :
  LVFree x ∈ dom Σ -> LVFree y ∈ dom Σ -> tm_lvars e ⊆ dom Σ ->
  tm_lvars e ⊆ dom (relevant_env Σ
    (polarity_ty pol TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) e) /\
  ({[x;y]} : aset) ⊆ lvars_fv (dom (relevant_env Σ
    (polarity_ty pol TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) e)).
Proof.
  intros Hx Hy He.
  assert (Hcty : context_ty_lvars
    (polarity_ty pol TList (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0))) =
    ({[LVFree x;LVFree y]} : lvset)).
  { destruct pol; cbn [polarity_ty context_ty_lvars context_ty_lvars_at
      q_merge_graph qual_vars qual_lvars];
      rewrite !lvars_at_depth_union, !lvars_at_depth_singleton_free,
        !lvars_at_depth_singleton_bound0_succ; set_solver. }
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  rewrite !storeA_restrict_dom, Hcty. split; [set_solver|].
  intros z Hz. apply lvars_fv_elem. clear -Hx Hy Hz.
  assert (Hz' : LVFree z ∈ ({[LVFree x;LVFree y]} : lvset)) by set_solver.
  set_solver.
Qed.

Lemma merge_graph_joinable Γ f x y e :
  context_typing_wf ∅ Γ e (merge_graph_ty f x y) ->
  x ∈ dom (erase_ctx Γ) -> y ∈ dom (erase_ctx Γ) ->
  fiberwise_joinable_on {[x;y]}
    (ty_denote_under ∅ Γ (merge_graph_ty f x y) e).
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
  destruct (merge_graph_relevant true _ f x y e HxΣ HyΣ HeΣ) as [HeOver HXOver].
  destruct (merge_graph_relevant false _ f x y e HxΣ HyΣ HeΣ) as [HeUnder HXUnder].
  unfold ty_denote_under, ty_denote.
  change (fiberwise_joinable_on {[x;y]}
    (ty_denote_gas 2 (atom_env_to_lty_env (erase_ctx Γ)) (merge_graph_ty f x y) e)).
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_ty_guard_formula.
  - apply fiberwise_joinable_on_and.
    + eapply (fiberwise_joinable_on_ty_denote_gas_over {[x;y]} 1
        (atom_env_to_lty_env (erase_ctx Γ)) TList
        (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)) e);
        [apply atom_store_to_lvar_store_closed|exact Hlce|exact HeOver|exact HXOver].
    + eapply (fiberwise_joinable_on_ty_denote_gas_under {[x;y]} 1
        (atom_env_to_lty_env (erase_ctx Γ)) TList
        (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)) e);
        [apply atom_store_to_lvar_store_closed|exact Hlce|exact HeUnder|exact HXUnder].
Qed.


Lemma q_merge_graph_store f x y r s :
  qualifier_holds_store (q_merge_graph f (LVFree x) (LVFree y) (LVFree r)) s <->
  exists xs ys, s !! x = Some (IncorrectMerge.vlist xs) /\
    s !! y = Some (IncorrectMerge.vlist ys) /\
    s !! r = Some (IncorrectMerge.vlist (f xs ys)).
Proof.
  unfold qualifier_holds_store.
  cbn [q_merge_graph qual_lvars qual_prop].
  split.
  - intros [Hlc [Hscope H]]. unfold lstore_on_lift_store in H.
    cbn [lso_store storeAO_store] in H.
    setoid_rewrite storeA_restrict_lookup in H.
    rewrite !decide_True in H by set_solver.
    setoid_rewrite lstore_lift_free_lookup_free in H. exact H.
  - intros H. assert (Hscope : lvars_fv ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]}) ⊆ dom (s : StoreT)).
    { destruct H as [a [b [Hx [Hy Hr]]]].
      rewrite !lvars_fv_union,!lvars_fv_singleton_free.
      assert (x ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto).
      assert (y ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto).
      assert (r ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto). set_solver. }
    assert (Hlc : lc_lvars ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]})).
    { intros [j|a] Ha; [set_solver|exact I]. }
    exists Hlc,Hscope. unfold lstore_on_lift_store. cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by set_solver.
    setoid_rewrite lstore_lift_free_lookup_free. exact H.
Qed.
Lemma q_merge_graph_open_store f x y r s :
  r ∉ ({[x;y]} : aset) ->
  qualifier_holds_store (qual_open_atom 0 r (typed_result_qual TList
    (q_merge_graph f (LVFree x) (LVFree y) (LVBound 0)))) s <->
  exists xs ys, s !! x = Some (IncorrectMerge.vlist xs) /\
    s !! y = Some (IncorrectMerge.vlist ys) /\
    s !! r = Some (IncorrectMerge.vlist (f xs ys)).
Proof.
  intros Hr. rewrite q_merge_graph_typed,q_merge_graph_open.
  base_swap_normalize. apply q_merge_graph_store.
Qed.
