(** The original fixed-point worker has a precise ordinary-arrow type. *)
From CaseStudy Require Import MergeIncorrectness MergeTyping MergeGraph MergeReduction NatArithmeticTyping MayMustIndependentTyping.
From ContextTyping Require Import Typing TypingRegular NatCases ConstCases Conversion
  Subtyping BasicBindings PrimOpConcreteContext Soundness.
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeEquivTermBase BaseIntro.
From Stdlib Require Import List Lia.
Import ListNotations.
Definition merge_one_ctx x := CtxComma CtxEmpty (CtxBind x (CTOver TList qual_top)).
Definition merge_inner_ty x := CTArrow (CTOver TList qual_top)
  (precise_ty TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVBound 1) (LVBound 0))).
Definition merge_precise_ty := CTArrow (CTOver TList qual_top)
  (CTArrow (CTOver TList qual_top)
    (precise_ty TList (q_merge_graph IncorrectMerge.result (LVBound 2) (LVBound 1) (LVBound 0)))).
Lemma merge_precise_wf d D : wf_context_ty_at d D merge_precise_ty.
Proof.
  cbn [merge_precise_ty precise_ty over_ty under_ty wf_context_ty_at q_merge_graph qual_vars qual_lvars erase_ty].
  repeat split; try (apply qual_top_lvars_wf_at; lia); try reflexivity.
  all: unfold lvars_wf_at; intros [k|a] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.
Lemma merge_precise_open x :
  cty_open 0 x (CTArrow (CTOver TList qual_top)
    (precise_ty TList (q_merge_graph IncorrectMerge.result (LVBound 2) (LVBound 1) (LVBound 0)))) = merge_inner_ty x.
Proof.
  cbn [cty_open precise_ty over_ty under_ty merge_inner_ty].
  rewrite !q_merge_graph_open,qual_open_atom_top_on,set_swap_singleton. base_swap_normalize. reflexivity.
Qed.
Lemma merge_inner_open x y : x<>y ->
  cty_open 0 y (precise_ty TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVBound 1) (LVBound 0))) =
    merge_graph_ty IncorrectMerge.result x y.
Proof. intros Hxy. cbn [cty_open precise_ty over_ty under_ty merge_graph_ty].
  rewrite !q_merge_graph_open. base_swap_normalize. reflexivity. Qed.
Lemma merge_inner_wf d D x : x ∈ D -> wf_context_ty_at d D (merge_inner_ty x).
Proof.
  intros Hx. cbn [merge_inner_ty precise_ty over_ty under_ty wf_context_ty_at q_merge_graph qual_vars qual_lvars erase_ty].
  repeat split; try (apply qual_top_lvars_wf_at; lia); try reflexivity.
  all: unfold lvars_wf_at; intros [k|a] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.
Lemma merge_one_wf x : wf_ctx_under ∅ (merge_one_ctx x).
Proof. cbn [merge_one_ctx wf_ctx_under basic_ctx ctx_dom]. repeat split; try set_solver; apply qual_top_lvars_wf_at; lia. Qed.
Lemma merge_one_erasure x : erase_ctx (merge_one_ctx x) = {[x:=TBase TList]}.
Proof. cbn [merge_one_ctx erase_ctx]. unfold store_union,store_empty. apply map_empty_union. Qed.
Lemma merge_partial_precise_context_typed x :
  has_context_type concrete_Φ ∅ (merge_one_ctx x) (tret (IncorrectMerge.partial (vfvar x))) (merge_inner_ty x).
Proof.
  rewrite merge_partial_lam. unfold merge_inner_ty.
  eapply CT_Lam with (τx:=CTOver TList qual_top) (L:={[x]}).
  - split; [apply merge_one_wf|]. split.
    + apply merge_inner_wf. rewrite merge_one_erasure. apply elem_of_dom. exists (TBase TList). apply map_lookup_singleton.
    + apply TT_Ret. rewrite <- merge_partial_lam. apply merge_partial_basic.
      rewrite merge_one_erasure. apply map_lookup_singleton.
  - intros y Hy. rewrite merge_inner_open by (apply not_elem_of_singleton in Hy; congruence).
    change (has_context_type concrete_Φ ∅ (merge_top_ctx x y) (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_graph_ty IncorrectMerge.result x y)).
    apply merge_body_graph_context_typed.
    + apply not_elem_of_singleton in Hy; congruence.
    + apply nat_pair_ctx_wf; [apply not_elem_of_singleton in Hy; congruence|apply over_top_basic|apply over_top_basic].
    + reflexivity.
Qed.
Lemma merge_first_prefix xs : arithmetic_prefix
  (tapp_tm (tret IncorrectMerge.merge_value) (IncorrectMerge.vlist xs))
  (tret (IncorrectMerge.partial (IncorrectMerge.vlist xs))).
Proof.
  assert (Hbasic : tm_has_type ∅ (tapp_tm (tret IncorrectMerge.merge_value) (IncorrectMerge.vlist xs)) (TArrow TList TList)) by type_merge.
  pose proof (basic_typing_regular_tm _ _ _ Hbasic). do 3 merge_one. apply Prefix_refl.
Qed.
Lemma merge_partial_instantiate s x xs : s !! x=Some (IncorrectMerge.vlist xs) ->
  lstore_instantiate_tm (lstore_lift_free s) (tret (IncorrectMerge.partial (vfvar x))) =
  tret (IncorrectMerge.partial (IncorrectMerge.vlist xs)).
Proof. intros Hx. arithmetic_instantiate. setoid_rewrite Hx. vm_compute. reflexivity. Qed.
Lemma merge_first_instantiate s x xs : s !! x=Some (IncorrectMerge.vlist xs) ->
  lstore_instantiate_tm (lstore_lift_free s) (tapp_tm (tret IncorrectMerge.merge_value) (vfvar x)) =
  tapp_tm (tret IncorrectMerge.merge_value) (IncorrectMerge.vlist xs).
Proof. intros Hx. arithmetic_instantiate. setoid_rewrite Hx. vm_compute. reflexivity. Qed.
Lemma merge_first_precise_context_typed x :
  has_context_type concrete_Φ ∅ (merge_one_ctx x)
    (tapp_tm (tret IncorrectMerge.merge_value) (vfvar x)) (merge_inner_ty x).
Proof.
  eapply CT_Conv; [|apply merge_partial_precise_context_typed|].
  - split; [apply merge_one_wf|]. split.
    + apply merge_inner_wf. rewrite merge_one_erasure. apply elem_of_dom. exists (TBase TList). apply map_lookup_singleton.
    + eapply basic_typing_tapp_tm; [apply TT_Ret,merge_value_basic|apply VT_FVar; rewrite merge_one_erasure; apply map_lookup_singleton].
  - intros m Hctx.
    assert (Hlookup : forall s,(m : WorldT) s -> exists xs,s !! x=Some (IncorrectMerge.vlist xs)).
    { intros s Hs. destruct (ctx_denote_under_lookup_typed ∅ (merge_one_ctx x) x (TBase TList) m s
        (merge_one_wf x) ltac:(rewrite merge_one_erasure; apply map_lookup_singleton) Hctx Hs) as [v [Hv Hty]].
      destruct (basic_typing_list_canonical_form v Hty) as [xs ->]. eauto. }
    split.
    + intros s v Hs. destruct (Hlookup s Hs) as [xs Hxs]. unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs)) v).
    + intros s Hs. destruct (Hlookup s Hs) as [xs Hxs].
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs))).
Qed.
Theorem merge_worker_precise_context_typed :
  has_context_type concrete_Φ ∅ CtxEmpty (tret IncorrectMerge.merge_value) merge_precise_ty.
Proof.
  unfold merge_precise_ty. eapply CT_ArrowIntro with (L:=∅).
  - split; [constructor|]. split; [apply merge_precise_wf|apply TT_Ret,merge_value_basic].
  - intros x _. rewrite merge_precise_open. apply merge_first_precise_context_typed.
Qed.
Corollary merge_worker_precise_context_sound :
  ctx_denote_under ∅ CtxEmpty ⊫ ty_denote_under ∅ CtxEmpty merge_precise_ty (tret IncorrectMerge.merge_value).
Proof. apply concrete_Fundamental,merge_worker_precise_context_typed. Qed.

(** The three finite traces of p.25, under ordinary sorted-input arrows. *)
From CaseStudy Require Import MergeTraceQualifier MayMustTyping.
From ContextTyping Require Import OverConsequence.
From Denotation Require Import OverConsequence.
Definition merge_trace_body_ty x y := CTOver TList
  (q_merge_relation merge_trace_relation (LVFree x) (LVFree y) (LVBound 0)).
Lemma merge_trace_body_wf d D x y : x ∈ D -> y ∈ D ->
  wf_context_ty_at d D (merge_trace_body_ty x y).
Proof.
  intros Hx Hy. cbn [merge_trace_body_ty wf_context_ty_at q_merge_relation qual_vars qual_lvars].
  unfold lvars_wf_at. intros [j|z] Hz; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.
Lemma merge_graph_trace_subtype Γ x y :
  wf_ctx_under ∅ Γ -> x ∈ dom (erase_ctx Γ) -> y ∈ dom (erase_ctx Γ) ->
  sub_type_under ∅ Γ
    (CTOver TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0)))
    (merge_trace_body_ty x y).
Proof.
  intros HΓ Hx Hy. apply sub_type_over_store_consequence.
  - exact HΓ.
  - exact (proj1 (merge_graph_wf 0 _ IncorrectMerge.result x y Hx Hy)).
  - apply merge_trace_body_wf; assumption.
  - intros m r s v Hctx Hs Hr Hq.
    assert (Hfresh : r ∉ ({[x;y]} : aset)).
    { pose proof (ctx_denote_under_store_scope ∅ Γ m s Hctx Hs) as Hscope.
      change (dom (erase_ctx Γ) ⊆ (dom (s : gmap atom value) : aset)) in Hscope.
      rewrite (wfworld_store_dom m s Hs) in Hscope. set_solver. }
    apply (q_merge_graph_open_store _ _ _ _ _ Hfresh) in Hq.
    apply (q_merge_relation_open_store _ _ _ _ _ Hfresh).
    destruct Hq as [xs [ys [Hsx [Hsy Hsr]]]].
    exists xs,ys,(IncorrectMerge.result xs ys). repeat split; try assumption; apply merge_result_trace.
Qed.
Lemma merge_body_trace_context_typed Φ Γ x y : x<>y ->
  wf_ctx_under ∅ Γ -> erase_ctx Γ=erase_ctx (merge_fixed_ctx x y [] []) ->
  has_context_type Φ ∅ Γ (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_trace_body_ty x y).
Proof.
  intros Hxy HΓ Herase.
  destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl) as [Hx Hy].
  change (erase_ctx (merge_fixed_ctx x y [] []) !! x=Some (TBase TList)) in Hx.
  change (erase_ctx (merge_fixed_ctx x y [] []) !! y=Some (TBase TList)) in Hy.
  rewrite <- Herase in Hx,Hy.
  assert (Hxd : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hyd : y ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  eapply CT_Sub.
  - split; [exact HΓ|]. split; [apply merge_trace_body_wf; assumption|apply merge_body_basic; assumption].
  - apply typing_inter_l with
      (τ2:=CTUnder TList (q_merge_graph IncorrectMerge.result (LVFree x) (LVFree y) (LVBound 0))).
    apply merge_body_graph_context_typed; assumption.
  - apply merge_graph_trace_subtype; assumption.
Qed.

Definition merge_sorted_one_ctx x := CtxComma CtxEmpty (CtxBind x (merge_list_over sorted)).
Definition merge_trace_inner_ty x := CTArrow (merge_list_over sorted)
  (CTOver TList (q_merge_relation merge_trace_relation (LVFree x) (LVBound 1) (LVBound 0))).
Definition merge_trace_ty := CTArrow (merge_list_over sorted)
  (CTArrow (merge_list_over sorted)
    (CTOver TList (q_merge_relation merge_trace_relation (LVBound 2) (LVBound 1) (LVBound 0)))).
Lemma merge_trace_wf d D : wf_context_ty_at d D merge_trace_ty.
Proof.
  cbn [merge_trace_ty precise_ty over_ty under_ty wf_context_ty_at q_merge_relation qual_vars qual_lvars erase_ty].
  repeat split; try (apply merge_list_wf; lia); try reflexivity.
  all: unfold lvars_wf_at; intros [k|a] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.
Lemma merge_trace_open x :
  cty_open 0 x (CTArrow (merge_list_over sorted)
    (CTOver TList (q_merge_relation merge_trace_relation (LVBound 2) (LVBound 1) (LVBound 0)))) = merge_trace_inner_ty x.
Proof.
  change (CTArrow (cty_open 0 x (merge_list_over sorted))
    (cty_open 1 x (CTOver TList (q_merge_relation merge_trace_relation (LVBound 2) (LVBound 1) (LVBound 0)))) = merge_trace_inner_ty x).
  rewrite mm_closed_type_open by apply merge_list_wf.
  cbn [cty_open merge_trace_inner_ty]. rewrite !q_merge_relation_open. base_swap_normalize. reflexivity.
Qed.
Lemma merge_trace_inner_open x y : x<>y ->
  cty_open 0 y (CTOver TList (q_merge_relation merge_trace_relation (LVFree x) (LVBound 1) (LVBound 0))) =
    merge_trace_body_ty x y.
Proof. intros Hxy. cbn [cty_open precise_ty over_ty under_ty merge_graph_ty].
  rewrite !q_merge_relation_open. base_swap_normalize. reflexivity. Qed.
Lemma merge_trace_inner_wf d D x : x ∈ D -> wf_context_ty_at d D (merge_trace_inner_ty x).
Proof.
  intros Hx. cbn [merge_trace_inner_ty precise_ty over_ty under_ty wf_context_ty_at q_merge_relation qual_vars qual_lvars erase_ty].
  repeat split; try (apply merge_list_wf; lia); try reflexivity.
  all: unfold lvars_wf_at; intros [k|a] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.
Lemma merge_sorted_one_wf x : wf_ctx_under ∅ (merge_sorted_one_ctx x).
Proof. cbn [merge_sorted_one_ctx wf_ctx_under basic_ctx ctx_dom]. repeat split; try set_solver; apply merge_list_wf; lia. Qed.
Lemma merge_sorted_one_erasure x : erase_ctx (merge_sorted_one_ctx x) = {[x:=TBase TList]}.
Proof. cbn [merge_sorted_one_ctx erase_ctx]. unfold store_union,store_empty. apply map_empty_union. Qed.
Lemma merge_partial_trace_context_typed x :
  has_context_type concrete_Φ ∅ (merge_sorted_one_ctx x) (tret (IncorrectMerge.partial (vfvar x))) (merge_trace_inner_ty x).
Proof.
  rewrite merge_partial_lam. unfold merge_trace_inner_ty.
  eapply CT_Lam with (τx:=merge_list_over sorted) (L:={[x]}).
  - split; [apply merge_sorted_one_wf|]. split.
    + apply merge_trace_inner_wf. rewrite merge_sorted_one_erasure. apply elem_of_dom. exists (TBase TList). apply map_lookup_singleton.
    + apply TT_Ret. rewrite <- merge_partial_lam. apply merge_partial_basic.
      rewrite merge_sorted_one_erasure. apply map_lookup_singleton.
  - intros y Hy. rewrite merge_trace_inner_open by (apply not_elem_of_singleton in Hy; congruence).
    change (has_context_type concrete_Φ ∅ (nat_pair_ctx x y (merge_list_over sorted) (merge_list_over sorted)) (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_trace_body_ty x y)).
    apply merge_body_trace_context_typed.
    + apply not_elem_of_singleton in Hy; congruence.
    + apply nat_pair_ctx_wf; [apply not_elem_of_singleton in Hy; congruence|apply merge_list_wf|apply merge_list_wf].
    + reflexivity.
Qed.
Lemma merge_first_trace_context_typed x :
  has_context_type concrete_Φ ∅ (merge_sorted_one_ctx x)
    (tapp_tm (tret IncorrectMerge.merge_value) (vfvar x)) (merge_trace_inner_ty x).
Proof.
  eapply CT_Conv; [|apply merge_partial_trace_context_typed|].
  - split; [apply merge_sorted_one_wf|]. split.
    + apply merge_trace_inner_wf. rewrite merge_sorted_one_erasure. apply elem_of_dom. exists (TBase TList). apply map_lookup_singleton.
    + eapply basic_typing_tapp_tm; [apply TT_Ret,merge_value_basic|apply VT_FVar; rewrite merge_sorted_one_erasure; apply map_lookup_singleton].
  - intros m Hctx.
    assert (Hlookup : forall s,(m : WorldT) s -> exists xs,s !! x=Some (IncorrectMerge.vlist xs)).
    { intros s Hs. destruct (ctx_denote_under_lookup_typed ∅ (merge_sorted_one_ctx x) x (TBase TList) m s
        (merge_sorted_one_wf x) ltac:(rewrite merge_sorted_one_erasure; apply map_lookup_singleton) Hctx Hs) as [v [Hv Hty]].
      destruct (basic_typing_list_canonical_form v Hty) as [xs ->]. eauto. }
    split.
    + intros s v Hs. destruct (Hlookup s Hs) as [xs Hxs]. unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs)) v).
    + intros s Hs. destruct (Hlookup s Hs) as [xs Hxs].
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs))).
Qed.
Theorem merge_worker_trace_context_typed :
  has_context_type concrete_Φ ∅ CtxEmpty (tret IncorrectMerge.merge_value) merge_trace_ty.
Proof.
  unfold merge_trace_ty. eapply CT_ArrowIntro with (L:=∅).
  - split; [constructor|]. split; [apply merge_trace_wf|apply TT_Ret,merge_value_basic].
  - intros x _. rewrite merge_trace_open. apply merge_first_trace_context_typed.
Qed.
Corollary merge_worker_trace_context_sound :
  ctx_denote_under ∅ CtxEmpty ⊫ ty_denote_under ∅ CtxEmpty merge_trace_ty (tret IncorrectMerge.merge_value).
Proof. apply concrete_Fundamental,merge_worker_trace_context_typed. Qed.


Print Assumptions merge_worker_trace_context_typed.
Print Assumptions merge_worker_precise_context_typed.

From Denotation Require Import QualifierStore.
Lemma merge_relation_results R Γ x y e m :
  wf_ctx_under ∅ Γ -> tm_has_type (erase_ctx Γ) e (TBase TList) ->
  m ⊨ ty_denote_under ∅ Γ (CTOver TList (q_merge_relation R (LVFree x) (LVFree y) (LVBound 0))) e ->
  forall s v,(m : WorldT) s -> tm_eval_in_store s e v ->
  exists xs ys zs,s !! x=Some (IncorrectMerge.vlist xs) /\ s !! y=Some (IncorrectMerge.vlist ys) /\
    v=IncorrectMerge.vlist zs /\ R xs ys zs.
Proof.
  intros HΓ Hbasic Hden s v Hs Heval.
  set (r:=fresh (world_dom (m : WorldT) ∪ {[x;y]})).
  assert (Hr : r ∉ world_dom (m : WorldT) ∪ {[x;y]}) by apply is_fresh.
  assert (Hqdom : qual_dom (q_merge_relation R (LVFree x) (LVFree y) (LVBound 0))=({[x;y]} : aset)).
  { unfold qual_dom. cbn [q_merge_relation qual_lvars].
    rewrite !lvars_fv_union,!lvars_fv_singleton_free,lvars_fv_singleton_bound. set_solver. }
  pose proof (over_denote_elim_store_results 0 (atom_env_to_lty_env (erase_ctx Γ)) TList
    (q_merge_relation R (LVFree x) (LVFree y) (LVBound 0)) e m r
    (atom_store_to_lvar_store_closed _) (basic_typing_regular_tm _ _ _ Hbasic) Hden
    ltac:(rewrite Hqdom; exact Hr) s v Hs Heval) as Hq.
  rewrite q_merge_relation_open_store in Hq by (clear -Hr; set_solver).
  destruct Hq as [xs [ys [zs [Hx [Hy [Hv HR]]]]]] .
  change ((<[r:=v]> s : gmap atom value) !! x=Some (IncorrectMerge.vlist xs)) in Hx.
  change ((<[r:=v]> s : gmap atom value) !! y=Some (IncorrectMerge.vlist ys)) in Hy.
  change ((<[r:=v]> s : gmap atom value) !! r=Some (IncorrectMerge.vlist zs)) in Hv.
  assert (Hrx : r<>x) by (clear -Hr; set_solver).
  assert (Hry : r<>y) by (clear -Hr; set_solver).
  pose proof (eq_trans (eq_sym (map_lookup_insert_ne s r x v ltac:(congruence))) Hx) as Hsx.
  pose proof (eq_trans (eq_sym (map_lookup_insert_ne s r y v ltac:(congruence))) Hy) as Hsy.
  assert (Hrv : (<[r:=v]> s : gmap atom value) !! r=Some v) by apply map_lookup_insert.
  assert (Hv' : Some v=Some (IncorrectMerge.vlist zs))
    by exact (eq_trans (eq_sym Hrv) Hv).
  injection Hv' as Hv'. exists xs,ys,zs. auto.
Qed.


(** The finite trace alone suffices for the incorrectness consequence. *)
Lemma merge_trace_sum_subtype x y : x<>y ->
  sub_type_under ∅ (merge_sorted_inputs x y) (merge_trace_body_ty x y) merge_error_result.
Proof.
  intros Hxy. apply merge_error_subtype; [exact Hxy| |].
  - destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl) as [Hx Hy].
    apply merge_trace_body_wf; apply elem_of_dom; eauto.
  - intros e m Hbasic Hsource s v Hs Heval Hx' Hy'.
    destruct (merge_relation_results merge_trace_relation (merge_sorted_inputs x y) x y e m
      (merge_inputs_wf x y Hxy) Hbasic Hsource s v Hs Heval) as [xs [ys [zs [Hsx [Hsy [-> HR]]]]]].
    pose proof (eq_trans (eq_sym Hsx) Hx') as Hxs.
    pose proof (eq_trans (eq_sym Hsy) Hy') as Hys.
    unfold IncorrectMerge.vlist in Hxs,Hys.
    injection Hxs as Hxs. injection Hys as Hys. subst xs ys.
    destruct HR as [_ [_ Hbug]]. specialize (Hbug (conj eq_refl eq_refl)). subst zs.
    exists [1;3;2;4]. split; [reflexivity|exact merge_trace_unsorted].
Qed.
Theorem merge_body_trace_incorrect_context_typed x y : x<>y ->
  has_context_type concrete_Φ ∅ (merge_sorted_inputs x y)
    (IncorrectMerge.body (vfvar x) (vfvar y)) merge_error_result.
Proof.
  intros Hxy. eapply CT_Sub.
  - split; [apply merge_inputs_wf; exact Hxy|]. split; [apply merge_error_wf|].
    apply merge_body_basic; destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl); assumption.
  - apply merge_body_trace_context_typed; [exact Hxy|apply merge_inputs_wf; exact Hxy|reflexivity].
  - apply merge_trace_sum_subtype. exact Hxy.
Qed.
Print Assumptions merge_body_trace_incorrect_context_typed.
