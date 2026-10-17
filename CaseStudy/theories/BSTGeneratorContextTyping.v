(** Top-level arrows are introduced before classifying the base result. *)
From CaseStudy Require Import BSTGeneratorProgram BSTGeneratorUnfolding BSTContext
  BSTSupport BSTCallTyping BSTRangeTyping NatArithmeticStages NatArithmeticTyping.
From ContextTyping Require Import Typing TypingRegular BasicBindings NatCases
  FiberSupport PrimOpConcreteContext Soundness.
From Denotation Require Import Context TypeEquivTermBase.
From ContextBasicDenotation Require Import TermSyntax TermEval.
From CoreLang Require Import BasicTypingProps.

Definition bst_top_ctx u v g : ctx :=
  CtxComma (nat_pair_ctx u v nat_over_ty nat_over_ty) (CtxBind g range_ty).

Lemma bst_top_ctx_wf u v g :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ (bst_top_ctx u v g).
Proof.
  intros Huv Hug Hvg. apply wf_ctx_comma_closed_bind.
  - apply nat_pair_ctx_wf; [exact Huv|apply nat_over_wf|apply nat_over_wf].
  - cbn [ctx_dom nat_pair_ctx]. clear -Hug Hvg. set_solver.
  - exact bst_range_ty_closed_wf.
Qed.

Definition bst_tree_range_lqual (r lo t : logic_var) : type_qualifier :=
  tqual ({[r]} ∪ {[lo]} ∪ {[t]}) (fun s => exists n a tr,
    lso_store s !! r = Some (vconst (cnat n)) /\
    lso_store s !! lo = Some (vconst (cnat a)) /\
    lso_store s !! t = Some (vconst (ctree tr)) /\ bst_spec n a tr).

Lemma bst_tree_range_lqual_value r lo t :
  bst_tree_range_lqual r lo t =
    q_tree_bst_range (bst_lvar_value r) (bst_lvar_value lo) (bst_lvar_value t).
Proof. destruct r,lo,t; reflexivity. Qed.

Lemma bst_tree_range_lqual_open r lo t j x :
  qual_open_atom j x (bst_tree_range_lqual r lo t) =
  bst_tree_range_lqual (swap (LVBound j) (LVFree x) r)
    (swap (LVBound j) (LVFree x) lo) (swap (LVBound j) (LVFree x) t).
Proof.
  apply qual_ext.
  - cbn [qual_open_atom bst_tree_range_lqual qual_lvars].
    rewrite !set_swap_union,!set_swap_singleton. reflexivity.
  - intros s1 s2 Hs. cbn [qual_open_atom bst_tree_range_lqual qual_prop].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value. setoid_rewrite Hs. reflexivity.
Qed.

Lemma bst_range_ty_open_closed k x : cty_open k x range_ty = range_ty.
Proof.
  apply (cty_open_above_lc_fresh 0 k x range_ty); [lia| |].
  - exact (wf_context_ty_at_lc 0 ∅ range_ty bst_range_ty_closed_wf).
  - rewrite bst_range_ty_fv. set_solver.
Qed.

Lemma bst_nat_over_open_closed k x : cty_open k x nat_over_ty = nat_over_ty.
Proof.
  apply (cty_open_above_lc_fresh 0 k x nat_over_ty); [lia| |].
  - exact (wf_context_ty_at_lc 0 ∅ nat_over_ty (nat_over_wf 0 ∅)).
  - rewrite nat_over_fv. set_solver.
Qed.

Definition bst_lo_function_ty u : context_ty :=
  CTArrow nat_over_ty (CTArrow range_ty
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vbvar 2) (vbvar 0)))).

Definition bst_range_function_result_ty u v : context_ty :=
  CTArrow range_ty (CTUnder TTree
    (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).

Lemma bst_generator_first_open u :
  cty_open 0 u (CTArrow nat_over_ty (CTArrow range_ty UBstBetween)) = bst_lo_function_ty u.
Proof.
  change (CTArrow (cty_open 0 u nat_over_ty) (CTArrow (cty_open 1 u range_ty)
    (CTUnder TTree (qual_open_atom 3 u
      (bst_tree_range_lqual (LVBound 3) (LVBound 2) (LVBound 0))))) = bst_lo_function_ty u).
  rewrite bst_nat_over_open_closed,bst_range_ty_open_closed,bst_tree_range_lqual_open.
  rewrite !swap_l. rewrite !swap_fresh by congruence.
  rewrite bst_tree_range_lqual_value. reflexivity.
Qed.

Lemma bst_generator_second_open u v :
  u <> v -> cty_open 0 v (CTArrow range_ty
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vbvar 2) (vbvar 0)))) =
  bst_range_function_result_ty u v.
Proof.
  intros Huv.
  change (CTArrow (cty_open 0 v range_ty) (CTUnder TTree
    (qual_open_atom 2 v (bst_tree_range_lqual (LVFree u) (LVBound 2) (LVBound 0)))) =
    bst_range_function_result_ty u v).
  rewrite bst_range_ty_open_closed,bst_tree_range_lqual_open.
  rewrite !swap_l. rewrite !swap_fresh by congruence.
  rewrite bst_tree_range_lqual_value. reflexivity.
Qed.

Lemma bst_generator_third_open u v g :
  u <> g -> v <> g ->
  cty_open 0 g (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))) =
    CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)).
Proof.
  intros Hug Hvg.
  change (CTUnder TTree (qual_open_atom 1 g
    (bst_tree_range_lqual (LVFree u) (LVFree v) (LVBound 0))) =
      CTUnder TTree (bst_tree_range_lqual (LVFree u) (LVFree v) (LVBound 0))).
  rewrite bst_tree_range_lqual_open. rewrite !swap_fresh by congruence. reflexivity.
Qed.

Lemma bst_top_ctx_lookups u v g :
  u <> v -> u <> g -> v <> g ->
  erase_ctx (bst_top_ctx u v g) !! u = Some (TBase TNat) /\
  erase_ctx (bst_top_ctx u v g) !! v = Some (TBase TNat) /\
  erase_ctx (bst_top_ctx u v g) !! g = Some BSTProgram.range_basic_ty.
Proof. intros Huv Hug Hvg. exact (bst_call_ctx_lookups 0 0 u v g Huv Hug Hvg). Qed.

Lemma bst_top_ctx_fiber_cover u v g :
  u <> v -> forall m σ mfib,
  m ⊨ ctx_denote_under ∅ (bst_top_ctx u v g) ->
  res_fiber_from_projection m {[u;v]} σ mfib ->
  exists n a, mfib ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g).
Proof.
  intros Huv m σ mfib Hctx Hfib.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hpair.
  pose proof (ctx_denote_comma_closed_right ∅ _ g range_ty m bst_range_ty_fv Hctx) as Hrange.
  destruct (nat_pair_fiber_constants u v σ m mfib Hpair Hfib) as [n [a Hfixed]].
  destruct (nat_pair_denote_inv ∅ u v _ _ mfib
    (nat_singleton_fv n) (nat_singleton_fv a) Hfixed) as [Hu Hv].
  exists n,a. apply bst_call_ctx_denote_intro; try assumption.
  exact (bst_range_binding_fiber g {[u;v]} σ m mfib Hrange Hfib).
Qed.

Lemma bst_open_body_top_context_typed u v g :
  u <> v -> u <> g -> v <> g ->
  has_context_type concrete_Φ ∅ (bst_top_ctx u v g)
    (bst_open_body (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros Huv Hug Hvg.
  pose proof (bst_top_ctx_wf u v g Huv Hug Hvg) as HΓ.
  destruct (bst_top_ctx_lookups u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  assert (Hwf : context_typing_wf ∅ (bst_top_ctx u v g)
    (bst_open_body (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))).
  { split; [exact HΓ|]. split.
    - apply q_bst_free_wf; apply elem_of_dom; eauto.
    - apply bst_open_body_variables_basic; assumption. }
  eapply CT_FiberCases with (I:=(nat*nat)%type)
    (cases:=fun na => bst_call_ctx (fst na) (snd na) u v g) (X:={[u;v]}).
  - exact Hwf.
  - intros [n a]. reflexivity.
  - intros [n a]. apply bst_open_body_minimal_context_typed; assumption.
  - apply context_under_fiberwise_joinable; [exact Hwf|].
    rewrite fv_under_qual,q_bst_free_dom.
    intros x Hx. apply elem_of_union. right. exact Hx.
  - intros m Hctx σ mfib Hfib.
    destruct (bst_top_ctx_fiber_cover u v g Huv m σ mfib Hctx Hfib) as [n [a Hcase]].
    exists (n,a). exact Hcase.
Qed.

Lemma bst_lo_function_wf D u :
  u ∈ D -> wf_context_ty_at 0 D (bst_lo_function_ty u).
Proof.
  intros Hu. rewrite <- bst_generator_first_open.
  eapply (wf_context_ty_at_mono_env 0 (∅ ∪ {[u]} : aset) D).
  - clear -Hu. set_solver.
  - apply wf_context_ty_at_open_at; [set_solver|].
  exact (proj2 bst_gen_ty_well_formed).
Qed.

Lemma bst_range_function_result_wf D u v :
  u <> v -> u ∈ D -> v ∈ D ->
  wf_context_ty_at 0 D (bst_range_function_result_ty u v).
Proof.
  intros Huv Hu Hv. rewrite <- bst_generator_second_open by exact Huv.
  eapply (wf_context_ty_at_mono_env 0 ({[u]} ∪ {[v]} : aset) D).
  - clear -Hu Hv. set_solver.
  - apply wf_context_ty_at_open_at; [clear -Huv; set_solver|].
  exact (proj2 (bst_lo_function_wf {[u]} u ltac:(set_solver))).
Qed.

Lemma bst_lower_partial_context_typed u v :
  u <> v ->
  has_context_type concrete_Φ ∅ (nat_pair_ctx u v nat_over_ty nat_over_ty)
    (tret (bst_lower_partial (vfvar u) (vfvar v))) (bst_range_function_result_ty u v).
Proof.
  intros Huv.
  pose proof (nat_pair_ctx_wf u v nat_over_ty nat_over_ty Huv
    (nat_over_wf 0 ∅) (nat_over_wf 0 ∅)) as HΓ.
  destruct (nat_pair_lookups u v nat_over_ty nat_over_ty Huv eq_refl eq_refl) as [Hu Hv].
  rewrite bst_lower_partial_lam. unfold bst_range_function_result_ty.
  eapply CT_Lam with (τx:=range_ty) (L:=({[u;v]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_range_function_result_wf; [exact Huv| |]; apply elem_of_dom; eauto.
    + apply TT_Ret. rewrite <- bst_lower_partial_lam.
      apply bst_lower_partial_variables_basic; assumption.
  - intros g Hg. rewrite bst_generator_third_open by (clear -Hg; set_solver).
    change (has_context_type concrete_Φ ∅ (bst_top_ctx u v g)
      (bst_open_body (vfvar u) (vfvar v) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))).
    apply bst_open_body_top_context_typed; [exact Huv| |]; clear -Hg; set_solver.
Qed.

Lemma bst_partial_context_typed u :
  has_context_type concrete_Φ ∅ (nat_one_ctx u)
    (tret (bst_partial (vfvar u))) (bst_lo_function_ty u).
Proof.
  rewrite bst_partial_lam. unfold bst_lo_function_ty.
  eapply CT_Lam with (τx:=nat_over_ty) (L:=({[u]} : aset)).
  - split; [apply nat_one_wf|]. split.
    + apply bst_lo_function_wf. rewrite nat_one_erasure. apply elem_of_dom.
      exists (TBase TNat). apply map_lookup_singleton.
    + apply TT_Ret. rewrite <- bst_partial_lam.
      apply bst_partial_variable_basic. rewrite nat_one_erasure. apply map_lookup_singleton.
  - intros v Hv. rewrite bst_generator_second_open by (clear -Hv; set_solver).
    change (has_context_type concrete_Φ ∅ (nat_pair_ctx u v nat_over_ty nat_over_ty)
      (tret (bst_lower_partial (vfvar u) (vfvar v))) (bst_range_function_result_ty u v)).
    apply bst_lower_partial_context_typed. clear -Hv. set_solver.
Qed.

Lemma bst_partial_instantiate σ u n :
  σ !! u = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ) (tret (bst_partial (vfvar u))) =
    tret (bst_partial (vnat n)).
Proof. intros Hu. arithmetic_instantiate. setoid_rewrite Hu. vm_compute. reflexivity. Qed.

Lemma bst_first_call_instantiate σ u n :
  σ !! u = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (tapp_tm (tret bst_gen_value) (vfvar u)) =
    tapp_tm (tret bst_gen_value) (vnat n).
Proof. intros Hu. arithmetic_instantiate. setoid_rewrite Hu. vm_compute. reflexivity. Qed.

Lemma bst_first_call_context_typed u :
  has_context_type concrete_Φ ∅ (nat_one_ctx u)
    (tapp_tm (tret bst_gen_value) (vfvar u)) (bst_lo_function_ty u).
Proof.
  pose proof (bst_partial_context_typed u) as Hpartial.
  pose proof (typing_wf_under _ _ _ _ _ Hpartial) as [HΓ [Hτ _]].
  eapply CT_Conv; [|exact Hpartial|].
  - split; [exact HΓ|]. split; [exact Hτ|].
    eapply basic_typing_tapp_tm; [apply TT_Ret|apply VT_FVar; rewrite nat_one_erasure; apply map_lookup_singleton].
    eapply basic_typing_weaken_value; [exact bst_gen_value_basic_typed|apply map_empty_subseteq].
  - intros m Hctx. split.
    + intros σ w Hσ. destruct (nat_one_lookup u m Hctx σ Hσ) as [n Hun].
      unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (bst_partial_instantiate σ u n Hun),(bst_first_call_instantiate σ u n Hun).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _ (bst_partial_prefix n)) w).
    + intros σ Hσ. destruct (nat_one_lookup u m Hctx σ Hσ) as [n Hun].
      rewrite (bst_partial_instantiate σ u n Hun),(bst_first_call_instantiate σ u n Hun).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _ (bst_partial_prefix n))).
Qed.

Theorem bst_gen_context_typed :
  has_context_type concrete_Φ ∅ CtxEmpty bst_gen_program bst_gen_ty.
Proof.
  unfold bst_gen_program,bst_gen_ty. apply CT_PersistIntro.
  - split; [constructor|]. split; [exact bst_gen_ty_well_formed|exact bst_gen_basic_typed].
  - exact empty_context_persistent.
  - eapply CT_ArrowIntro with (L:=∅).
    + split; [constructor|]. split; [exact bst_gen_ty_well_formed|exact bst_gen_basic_typed].
    + intros u _. rewrite bst_generator_first_open. apply bst_first_call_context_typed.
Qed.

Theorem bst_gen_type_judgement_holds : bst_gen_type_judgement.
Proof. exact bst_gen_context_typed. Qed.

Corollary bst_gen_denotational_sound :
  ctx_denote_under ∅ CtxEmpty ⊫
    ty_denote_under ∅ CtxEmpty bst_gen_ty bst_gen_program.
Proof. apply concrete_Fundamental. exact bst_gen_context_typed. Qed.
