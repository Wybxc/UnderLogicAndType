(** Revised pp. 24--25: independent sorted inputs expose an unsorted result. *)
From CaseStudy Require Import MergeTyping MergeReduction MergeGraph MayMustWorlds
  MayMustBase MayMustTyping MayMustIndependentCases MayMustIndependentTyping.
From ContextTyping Require Import Typing TypingRegular NatCases ConstCases Subtyping
  SoundnessLam SoundnessMatch Soundness PrimOpConcreteContext BasicBindings.
From Denotation Require Import Context TypeEquiv TypeEquivCore OverConsequence BaseCoverage
  ResultQualifier QualifierStore BaseIntro ConditionalCoverage.
From ContextBasicDenotation Require Import TermTLet.
From Stdlib Require Import List Lia Classical_Prop.
Import ListNotations.

Definition merge_list_qual (P : list nat -> Prop) :=
  param_result_qual TList ∅ (fun _ v => exists xs, v=IncorrectMerge.vlist xs /\ P xs).
Definition merge_list_under P := CTUnder TList (merge_list_qual P).
Definition merge_list_over P := CTOver TList (merge_list_qual P).
Definition merge_sorted_inputs x y :=
  CtxStar (CtxStar CtxEmpty (CtxBind x (merge_list_under sorted)))
    (CtxBind y (merge_list_under sorted)).
Definition merge_error_result := CTSum (merge_list_over (fun xs => ~sorted xs)) (CTOver TList qual_top).
Definition merge_incorrect_ty := CTWand (merge_list_under sorted)
  (CTWand (merge_list_under sorted) merge_error_result).
Definition merge_top_ctx x y := nat_pair_ctx x y (CTOver TList qual_top) (CTOver TList qual_top).

Lemma merge_list_wf d D P : wf_context_ty_at d D (merge_list_under P).
Proof. apply param_result_qual_wf. set_solver. Qed.
Lemma merge_list_fv pol P : fv_cty (polarity_ty pol TList (merge_list_qual P))=∅.
Proof. destruct pol; pose proof (basic_context_ty_fv_subset ∅ _ (merge_list_wf 0 ∅ P)); set_solver. Qed.
Lemma merge_list_open_store P r s :
  qualifier_holds_store (qual_open_atom 0 r (typed_result_qual TList (merge_list_qual P))) s <->
  exists xs,s !! r=Some (IncorrectMerge.vlist xs) /\ P xs.
Proof.
  unfold merge_list_qual. rewrite typed_param_result_qual,param_result_qual_open_store by set_solver.
  split.
  - intros [_ [v [Hv [_ [xs [-> HP]]]]]]. eauto.
  - intros [xs [Hx HP]]. split; [set_solver|]. exists (IncorrectMerge.vlist xs).
    repeat split; try assumption; [apply BVT_Const|exists xs; auto].
Qed.
Lemma merge_sorted_covers x (m : WfWorldT) xs :
  m ⊨ ctx_denote_under ∅ (CtxBind x (merge_list_under sorted)) -> sorted xs ->
  exists s,(m : WorldT) s /\ s !! x=Some (IncorrectMerge.vlist xs).
Proof.
  intros Hctx HP. rewrite ctx_denote_closed_bind in Hctx by apply (merge_list_fv false).
  apply res_models_and_iff in Hctx as [_ Hden]. destruct (world_wf m) as [[s Hs] _].
  destruct (under_ret_var_covers_value 0 (atom_env_to_lty_env {[x:=TBase TList]}) TList
    (merge_list_qual sorted) x m s (IncorrectMerge.vlist xs)
    (atom_store_to_lvar_store_closed _) ltac:(unfold merge_list_qual; rewrite param_result_qual_dom; set_solver)
    Hden Hs) as [t [Ht [_ Htx]]].
  - rewrite merge_list_open_store. exists xs. split; [apply map_lookup_insert|exact HP].
  - eauto.
Qed.
Lemma merge_inputs_wf x y : x<>y -> wf_ctx_under ∅ (merge_sorted_inputs x y).
Proof.
  intros Hxy. cbn [merge_sorted_inputs wf_ctx_under basic_ctx ctx_dom].
  repeat split; try set_solver; apply merge_list_wf.
Qed.
Lemma merge_inputs_erasure x y :
  erase_ctx (merge_sorted_inputs x y)=erase_ctx (merge_fixed_ctx x y [] []).
Proof. reflexivity. Qed.
Lemma merge_top_wf x y : x<>y -> wf_ctx_under ∅ (merge_top_ctx x y).
Proof. intros Hxy. apply nat_pair_ctx_wf; [exact Hxy|apply over_top_basic|apply over_top_basic]. Qed.
Lemma merge_top_denote_subset Γ x y (m n : WfWorldT) :
  x<>y -> wf_ctx_under ∅ Γ -> erase_ctx Γ=erase_ctx (merge_top_ctx x y) ->
  m ⊨ ctx_denote_under ∅ Γ -> res_subset n m ->
  n ⊨ ctx_denote_under ∅ (merge_top_ctx x y).
Proof.
  intros Hxy HΓ HE Hctx Hsub.
  destruct (merge_pair_list_lookups x y (CTOver TList qual_top) (CTOver TList qual_top) Hxy eq_refl eq_refl) as [Hx Hy].
  change (erase_ctx (merge_top_ctx x y) !! x=Some (TBase TList)) in Hx.
  change (erase_ctx (merge_top_ctx x y) !! y=Some (TBase TList)) in Hy.
  rewrite <- HE in Hx,Hy.
  apply nat_pair_denote_intro;
    [apply over_top_basic|(pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic TList)); set_solver)|(pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic TList)); set_solver)| |].
  all: apply over_top_bind_denote_from_basic_world;
    eapply basic_world_formula_res_subset; [exact Hsub|];
    eapply ctx_denote_under_basic_singleton; eauto.
Qed.

Lemma merge_inputs_pair_covers x y (m : WfWorldT) xs ys :
  m ⊨ ctx_denote_under ∅ (merge_sorted_inputs x y) -> sorted xs -> sorted ys ->
  exists s,(m : WorldT) s /\ s !! x=Some (IncorrectMerge.vlist xs) /\ s !! y=Some (IncorrectMerge.vlist ys).
Proof.
  intros Hctx Hxs Hys.
  destruct (ctx_denote_under_star_elim ∅ _ _ m Hctx) as [c [d [Hcd [Hle [Hc Hd]]]]].
  destruct (ctx_denote_under_star_elim ∅ _ _ c Hc) as [a [b [Hab [Habc [_ Hb]]]]].
  assert (Hcx : c ⊨ ctx_denote_under ∅ (CtxBind x (merge_list_under sorted))).
  { eapply res_models_kripke; [|exact Hb]. etransitivity; [apply res_product_le_r|exact Habc]. }
  destruct (merge_sorted_covers x c xs Hcx Hxs) as [sx [Hsx Hxx]].
  destruct (merge_sorted_covers y d ys Hd Hys) as [sy [Hsy Hyy]].
  assert (Hprod : (res_product c d Hcd : WorldT) (sx ∪ sy)).
  { exists sx,sy. split; [exact Hsx|]. split; [exact Hsy|]. split; [exact (Hcd sx sy Hsx Hsy)|reflexivity]. }
  assert (Hxunion : (sx ∪ sy : gmap atom value) !! x=Some (IncorrectMerge.vlist xs)).
  { apply map_lookup_union_Some_raw. left. exact Hxx. }
  assert (Hyunion : (sx ∪ sy : gmap atom value) !! y=Some (IncorrectMerge.vlist ys)).
  { assert (Hyd : y ∈ dom (sy : gmap atom value)) by (apply elem_of_dom; eauto).
    exact (eq_trans (mm_union_lookup_right sx sy y (Hcd sx sy Hsx Hsy) Hyd) Hyy). }
  rewrite <- (res_restrict_eq_of_le _ _ Hle) in Hprod.
  destruct Hprod as [s [Hs Hproj]]. exists s. split; [exact Hs|].
  change (store_restrict s (world_dom (res_product c d Hcd : WorldT)) = sx ∪ sy) in Hproj.
  split.
  - assert (Hr : (store_restrict s (world_dom (res_product c d Hcd : WorldT)) : StoreT) !! x=Some (IncorrectMerge.vlist xs))
      by (rewrite Hproj; exact Hxunion).
    exact (proj2 (storeA_restrict_lookup_some s _ x _ Hr)).
  - assert (Hr : (store_restrict s (world_dom (res_product c d Hcd : WorldT)) : StoreT) !! y=Some (IncorrectMerge.vlist ys))
      by (rewrite Hproj; exact Hyunion).
    exact (proj2 (storeA_restrict_lookup_some s _ y _ Hr)).
Qed.

Lemma merge_graph_results Γ x y e m :
  wf_ctx_under ∅ Γ -> tm_has_type (erase_ctx Γ) e (TBase TList) ->
  m ⊨ ty_denote_under ∅ Γ (CTOver TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0))) e ->
  forall s v,(m : WorldT) s -> tm_eval_in_store s e v ->
  exists xs ys,s !! x=Some (IncorrectMerge.vlist xs) /\ s !! y=Some (IncorrectMerge.vlist ys) /\
    v=IncorrectMerge.vlist (IncorrectMerge.result xs ys).
Proof.
  intros HΓ Hbasic Hden s v Hs Heval.
  set (r:=fresh (world_dom (m : WorldT) ∪ {[x;y]})).
  assert (Hr : r ∉ world_dom (m : WorldT) ∪ {[x;y]}) by apply is_fresh.
  assert (Hqdom : qual_dom (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0))=({[x;y]} : aset)).
  { unfold qual_dom. cbn [q_merge_graph qual_lvars].
    rewrite !lvars_fv_union,!lvars_fv_singleton_free,lvars_fv_singleton_bound. set_solver. }
  pose proof (over_denote_elim_store_results 0 (atom_env_to_lty_env (erase_ctx Γ)) TList
    (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0)) e m r
    (atom_store_to_lvar_store_closed _) (basic_typing_regular_tm _ _ _ Hbasic) Hden
    ltac:(rewrite Hqdom; exact Hr) s v Hs Heval) as Hq.
  rewrite q_merge_graph_open_store in Hq by (clear -Hr; set_solver).
  destruct Hq as [xs [ys [Hx [Hy Hv]]]].
  change ((<[r:=v]> s : gmap atom value) !! x=Some (IncorrectMerge.vlist xs)) in Hx.
  change ((<[r:=v]> s : gmap atom value) !! y=Some (IncorrectMerge.vlist ys)) in Hy.
  change ((<[r:=v]> s : gmap atom value) !! r=Some (IncorrectMerge.vlist (IncorrectMerge.result xs ys))) in Hv.
  assert (Hrx : r<>x) by (clear -Hr; set_solver).
  assert (Hry : r<>y) by (clear -Hr; set_solver).
  pose proof (eq_trans (eq_sym (map_lookup_insert_ne s r x v ltac:(congruence))) Hx) as Hsx.
  pose proof (eq_trans (eq_sym (map_lookup_insert_ne s r y v ltac:(congruence))) Hy) as Hsy.
  assert (Hrv : (<[r:=v]> s : gmap atom value) !! r=Some v) by apply map_lookup_insert.
  assert (Hv' : Some v=Some (IncorrectMerge.vlist (IncorrectMerge.result xs ys)))
    by exact (eq_trans (eq_sym Hrv) Hv).
  injection Hv' as Hv'. exists xs,ys. auto.
Qed.

(** Any Over certificate proving the selected input pair erroneous suffices.
    The rest of the input world supplies the nonempty top summand. *)
Lemma merge_error_subtype x y φ : x<>y ->
  wf_context_ty_at 0 (dom (erase_ctx (merge_sorted_inputs x y))) (CTOver TList φ) ->
  (forall e m, tm_has_type (erase_ctx (merge_sorted_inputs x y)) e (TBase TList) ->
    m ⊨ ty_denote_under ∅ (merge_sorted_inputs x y) (CTOver TList φ) e ->
    forall s v,(m : WorldT) s -> tm_eval_in_store s e v ->
      s !! x=Some (IncorrectMerge.vlist [1;2]) -> s !! y=Some (IncorrectMerge.vlist [3;4]) ->
      exists zs,v=IncorrectMerge.vlist zs /\ ~ sorted zs) ->
  sub_type_under ∅ (merge_sorted_inputs x y) (CTOver TList φ) merge_error_result.
Proof.
  intros Hxy Hφ Herror. set (Γ:=merge_sorted_inputs x y). set (Δ:=merge_top_ctx x y).
  assert (HΓ : wf_ctx_under ∅ Γ) by (apply merge_inputs_wf; exact Hxy).
  assert (HΔ : wf_ctx_under ∅ Δ) by (apply merge_top_wf; exact Hxy).
  assert (HE : erase_ctx Γ=erase_ctx Δ) by reflexivity.
  destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl) as [Hx Hy].
  assert (Hxd : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; exists (TBase TList); exact Hx).
  assert (Hyd : y ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; exists (TBase TList); exact Hy).
  assert (Htarget : wf_context_ty_at 0 (dom (erase_ctx Γ)) merge_error_result).
  { split; [apply merge_list_wf|]. split; [apply qual_top_lvars_wf_at; lia|reflexivity]. }
  apply sub_type_under_intro; [exact HΓ|exact Hφ|exact Htarget|reflexivity|].
  intros e m Hbasic Hctx Hsource.
  pose proof (ty_denote_under_total _ _ _ _ _ Hsource) as Htotal.
  assert (Hwf : context_typing_wf ∅ Γ e merge_error_result) by (split; [exact HΓ|split; assumption]).
  set (P:=fun s : StoreT => s !! x=Some (IncorrectMerge.vlist [1;2]) /\ s !! y=Some (IncorrectMerge.vlist [3;4])).
  assert (HP : exists s,(m : WorldT) s /\ P s).
  { destruct (merge_inputs_pair_covers x y m [1;2] [3;4] Hctx ltac:(cbn [sorted sorted_from]; lia)
      ltac:(cbn [sorted sorted_from]; lia)) as [s [Hs Hlook]]. exists s. auto. }
  assert (HnotP : exists s,(m : WorldT) s /\ ~P s).
  { destruct (merge_inputs_pair_covers x y m [] [] Hctx I I) as [s [Hs [Hsx Hsy]]].
    exists s. split; [exact Hs|]. intros [Hx' Hy']. pose proof (eq_trans (eq_sym Hsx) Hx') as Hbad. discriminate Hbad. }
  set (mt:=select_world m P HP). set (mf:=select_world m (fun s=>~P s) HnotP).
  destruct (select_world_partition m P HP HnotP) as [Hdef Hsum].
  unfold ty_denote_under,ty_denote.
  eapply ty_denote_gas_sum_intro_from_branch_refinement with (m1:=mt) (m2:=mf) (Hdef:=Hdef).
  - change (res_sum (select_world m P HP) (select_world m (fun s=>~P s) HnotP) Hdef ⊑ m).
    rewrite Hsum. reflexivity.
  - reflexivity.
  - cbn [cty_depth merge_error_result merge_list_over]. lia.
  - cbn [cty_depth merge_error_result merge_list_over]. lia.
  - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
  - exact Htotal.
  - apply over_denote_intro_store_results with (L:=(world_dom (m : WorldT) ∪ {[x;y]} : aset)).
    + apply (wf_context_ty_at_lc 0 _ _ (merge_list_wf 0 (dom (erase_ctx Γ)) (fun xs=>~sorted xs))).
    + apply ty_denote_gas_zero_of_guard,ty_guard_relevant_of_static_full_total.
      * assert (HctxT : mt ⊨ ctx_denote_under ∅ Δ) by
          (eapply merge_top_denote_subset; [exact Hxy|exact HΓ|exact HE|exact Hctx|apply select_world_subset]).
        rewrite HE. apply context_typing_wf_denot_static_guard_full with (Σ:=∅) (Γ:=Δ).
        -- split; [exact HΔ|]. split; [apply merge_list_wf|rewrite <- HE; exact Hbasic].
        -- exact HctxT.
      * eapply expr_total_formula_res_subset; [apply select_world_subset|exact Htotal].
    + intros r Hr s v [Hs HPs] Heval.
      destruct (Herror e m Hbasic Hsource s v Hs Heval (proj1 HPs) (proj2 HPs)) as [zs [-> Hbad]].
      rewrite merge_list_open_store. exists zs.
      split; [apply map_lookup_insert|exact Hbad].
  - apply ty_denote_gas_over_top_from_zero.
    apply ty_denote_gas_zero_of_guard,ty_guard_relevant_of_static_full_total.
    + assert (HctxF : mf ⊨ ctx_denote_under ∅ Δ) by
        (eapply merge_top_denote_subset; [exact Hxy|exact HΓ|exact HE|exact Hctx|apply select_world_subset]).
      rewrite HE. apply context_typing_wf_denot_static_guard_full with (Σ:=∅) (Γ:=Δ).
      * split; [exact HΔ|]. split; [apply qual_top_lvars_wf_at; lia|rewrite <- HE; exact Hbasic].
      * exact HctxF.
    + eapply expr_total_formula_res_subset; [apply select_world_subset|exact Htotal].
Qed.

Lemma merge_sum_subtype x y : x<>y ->
  sub_type_under ∅ (merge_sorted_inputs x y)
    (CTOver TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0)))
    merge_error_result.
Proof.
  intros Hxy. apply merge_error_subtype; [exact Hxy| |].
  - destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl) as [Hx Hy].
    assert (Hxd : x ∈ dom (erase_ctx (merge_sorted_inputs x y))) by (apply elem_of_dom; eauto).
    assert (Hyd : y ∈ dom (erase_ctx (merge_sorted_inputs x y))) by (apply elem_of_dom; eauto).
    exact (proj1 (merge_graph_wf 0 _ _ x y Hxd Hyd)).
  - intros e m Hbasic Hsource s v Hs Heval Hx' Hy'.
    destruct (merge_graph_results (merge_sorted_inputs x y) x y e m
      (merge_inputs_wf x y Hxy) Hbasic Hsource s v Hs Heval) as [xs [ys [Hsx [Hsy ->]]]].
    pose proof (eq_trans (eq_sym Hsx) Hx') as Hxs.
    pose proof (eq_trans (eq_sym Hsy) Hy') as Hys.
    unfold IncorrectMerge.vlist in Hxs,Hys.
    injection Hxs as Hxs. injection Hys as Hys. subst xs ys.
    exists [1;3;2;4]. split; [reflexivity|exact merge_trace_unsorted].
Qed.

Lemma merge_body_incorrect_context_typed x y : x<>y ->
  has_context_type concrete_Φ ∅ (merge_sorted_inputs x y)
    (IncorrectMerge.body (vfvar x) (vfvar y)) merge_error_result.
Proof.
  intros Hxy. eapply CT_Sub.
  - split; [apply merge_inputs_wf; exact Hxy|]. split.
    + split; [apply merge_list_wf|]. split; [apply qual_top_lvars_wf_at; lia|reflexivity].
    + apply merge_body_basic; destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl); assumption.
  - apply typing_inter_l with
      (τ2:=CTUnder TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0))).
    apply merge_body_graph_context_typed; [exact Hxy|apply merge_inputs_wf; exact Hxy|reflexivity].
  - apply merge_sum_subtype. exact Hxy.
Qed.
Lemma merge_error_wf d D : wf_context_ty_at d D merge_error_result.
Proof. split; [apply merge_list_wf|]. split; [apply qual_top_lvars_wf_at; lia|reflexivity]. Qed.
Lemma merge_incorrect_wf d D : wf_context_ty_at d D merge_incorrect_ty.
Proof. split; [apply merge_list_wf|]. split; [apply merge_list_wf|apply merge_error_wf]. Qed.
Lemma merge_partial_basic Δ x : Δ !! x=Some (TBase TList) ->
  value_has_type Δ (IncorrectMerge.partial (vfvar x)) (TArrow TList TList).
Proof. intros Hx. assert (Hxdom : x ∈ dom Δ) by (apply elem_of_dom; eauto). type_merge. Qed.
Lemma merge_partial_lam vx : IncorrectMerge.partial vx =
  vlam TList (match IncorrectMerge.partial vx with vlam _ e=>e|_=>tret (vconst cunit) end).
Proof. reflexivity. Qed.
Lemma merge_partial_open x y :
  open_tm 0 (vfvar y) (match IncorrectMerge.partial (vfvar x) with vlam _ e=>e|_=>tret (vconst cunit) end) =
    IncorrectMerge.body (vfvar x) (vfvar y).
Proof. reflexivity. Qed.
Lemma merge_inner_incorrect_context_typed x :
  has_context_type concrete_Φ ∅ (CtxStar CtxEmpty (CtxBind x (merge_list_under sorted)))
    (tret (IncorrectMerge.partial (vfvar x))) (CTWand (merge_list_under sorted) merge_error_result).
Proof.
  rewrite merge_partial_lam.
  eapply CT_LamD with (τx:=merge_list_under sorted) (L:={[x]}).
  - split.
    + cbn [wf_ctx_under basic_ctx ctx_dom]. repeat split; try set_solver; apply merge_list_wf.
    + split; [split; [apply merge_list_wf|apply merge_error_wf]|].
      apply TT_Ret. rewrite <- merge_partial_lam. apply merge_partial_basic.
      change ((∅ ∪ {[x:=TBase TList]} : gmap atom ty) !! x=Some (TBase TList)).
      unfold store_union,store_empty. rewrite map_empty_union. apply map_lookup_singleton.
  - intros y Hy. rewrite mm_closed_type_open by apply merge_error_wf.
    change (has_context_type concrete_Φ ∅ (merge_sorted_inputs x y)
      (IncorrectMerge.body (vfvar x) (vfvar y)) merge_error_result).
    apply merge_body_incorrect_context_typed. apply not_elem_of_singleton in Hy. congruence.
Qed.

Print Assumptions merge_body_incorrect_context_typed.
