(** Genuine syntax derivations for the list merge's exact graph. *)
From CaseStudy Require Import MergeReduction MergeGraph NatArithmeticTyping MayMustIndependentCases.
From ContextTyping Require Import Typing TypingRegular NatCases ConstCases Conversion Subtyping
  BasicBindings PrimOpConcreteContext Soundness.
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeEquivTermBase.
From Stdlib Require Import List Lia.
Import ListNotations.

Lemma merge_instance_context_typed Φ xs ys :
  has_context_type Φ ∅ CtxEmpty (IncorrectMerge.call xs ys)
    (merge_singleton_ty (IncorrectMerge.result xs ys)).
Proof.
  eapply CT_Conv with (e1:=tret (IncorrectMerge.vlist (IncorrectMerge.result xs ys))).
  - split; [constructor|]. split; [apply merge_singleton_wf|apply merge_call_basic].
  - apply CT_Const. split; [constructor|]. split; [apply merge_singleton_wf|apply TT_Ret,VT_Const].
  - intros m _. destruct (arithmetic_prefix_equivalence _ _ (merge_call_prefix xs ys)) as [Hrun Htotal].
    split.
    + intros s v _. unfold tm_eval_in_store,expr_eval_in_store.
      rewrite !instantiate_closed_tm by (first [reflexivity|eapply basic_typing_closed_tm; apply merge_call_basic]).
      symmetry. apply Hrun.
    + intros s _. rewrite !instantiate_closed_tm by
        (first [reflexivity|eapply basic_typing_closed_tm; apply merge_call_basic]).
      symmetry. exact Htotal.
Qed.
Lemma merge_body_closed_basic xs ys :
  tm_has_type ∅ (IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys)) (TBase TList).
Proof. type_merge. Qed.
Lemma merge_body_closed_context_typed Φ xs ys :
  has_context_type Φ ∅ CtxEmpty
    (IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys))
    (merge_singleton_ty (IncorrectMerge.result xs ys)).
Proof.
  eapply CT_Conv; [|apply merge_instance_context_typed|].
  - split; [constructor|]. split; [apply merge_singleton_wf|apply merge_body_closed_basic].
  - intros m _. destruct (arithmetic_prefix_equivalence _ _ (merge_call_body_prefix xs ys)) as [Hrun Htotal].
    split.
    + intros s v _. unfold tm_eval_in_store,expr_eval_in_store.
      rewrite !instantiate_closed_tm by (eapply basic_typing_closed_tm;
        first [apply merge_call_basic|apply merge_body_closed_basic]). apply Hrun.
    + intros s _. rewrite !instantiate_closed_tm by (eapply basic_typing_closed_tm;
        first [apply merge_call_basic|apply merge_body_closed_basic]). exact Htotal.
Qed.

Definition merge_fixed_ctx x y xs ys :=
  nat_pair_ctx x y (merge_singleton_ty xs) (merge_singleton_ty ys).
Lemma merge_fixed_lookups x y xs ys m :
  m ⊨ ctx_denote_under ∅ (merge_fixed_ctx x y xs ys) ->
  (forall s, (m : WorldT) s -> s !! x = Some (IncorrectMerge.vlist xs)) /\
  (forall s, (m : WorldT) s -> s !! y = Some (IncorrectMerge.vlist ys)).
Proof.
  intros Hctx. destruct (nat_pair_denote_inv ∅ x y _ _ m
    (const_precise_fv (clist xs)) (const_precise_fv (clist ys)) Hctx) as [Hx Hy].
  split; eapply const_precise_bind_lookup; eauto.
Qed.
Lemma merge_pair_list_lookups x y τx τy :
  x<>y -> erase_ty τx=TBase TList -> erase_ty τy=TBase TList ->
  erase_ctx (nat_pair_ctx x y τx τy) !! x = Some (TBase TList) /\
  erase_ctx (nat_pair_ctx x y τx τy) !! y = Some (TBase TList).
Proof.
  intros Hxy Hx Hy. cbn [nat_pair_ctx erase_ctx]. rewrite Hx,Hy.
  unfold store_union,store_empty. rewrite map_empty_union.
  split; apply map_lookup_union_Some_raw; [left; apply lookup_singleton_eq|].
  right. split; [apply lookup_singleton_ne; congruence|apply lookup_singleton_eq].
Qed.
Lemma merge_body_instantiate s x y xs ys :
  s !! x = Some (IncorrectMerge.vlist xs) -> s !! y = Some (IncorrectMerge.vlist ys) ->
  lstore_instantiate_tm (lstore_lift_free s) (IncorrectMerge.body (vfvar x) (vfvar y)) =
    IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys).
Proof. intros Hx Hy. arithmetic_instantiate. setoid_rewrite Hx. setoid_rewrite Hy. vm_compute. reflexivity. Qed.
Lemma merge_body_fixed_context_typed Φ x y xs ys : x<>y ->
  has_context_type Φ ∅ (merge_fixed_ctx x y xs ys)
    (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_graph_ty IncorrectMerge.result x y).
Proof.
  intros Hxy. set (Γ:=merge_fixed_ctx x y xs ys).
  assert (HΓ : wf_ctx_under ∅ Γ) by (apply nat_pair_ctx_wf; [exact Hxy|apply merge_singleton_wf|apply merge_singleton_wf]).
  destruct (merge_pair_list_lookups x y (merge_singleton_ty xs) (merge_singleton_ty ys) Hxy eq_refl eq_refl) as [Hx Hy].
  change (erase_ctx Γ !! x=Some (TBase TList)) in Hx.
  change (erase_ctx Γ !! y=Some (TBase TList)) in Hy.
  assert (Hxd : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hyd : y ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hbasic : tm_has_type (erase_ctx Γ) (IncorrectMerge.body (vfvar x) (vfvar y)) (TBase TList))
    by (apply merge_body_basic; assumption).
  eapply CT_Sub.
  - split; [exact HΓ|]. split; [apply merge_graph_wf; assumption|exact Hbasic].
  - eapply CT_Conv with (e1:=IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys)).
    + split; [exact HΓ|]. split; [apply merge_singleton_wf|exact Hbasic].
    + apply typing_closed_weaken; [exact HΓ|apply merge_body_closed_context_typed].
    + intros m Hctx. destruct (merge_fixed_lookups x y xs ys m Hctx) as [Hsx Hsy].
      assert (Hclosed : fv_tm (IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys))=∅)
        by (eapply basic_typing_closed_tm; apply merge_body_closed_basic).
      split.
      * intros s v Hs. unfold tm_eval_in_store,expr_eval_in_store.
        rewrite instantiate_closed_tm by exact Hclosed.
        rewrite (merge_body_instantiate s x y xs ys (Hsx s Hs) (Hsy s Hs)). reflexivity.
      * intros s Hs. rewrite instantiate_closed_tm by exact Hclosed.
        rewrite (merge_body_instantiate s x y xs ys (Hsx s Hs) (Hsy s Hs)). reflexivity.
  - apply merge_graph_refine_singleton; try assumption.
    intros m Hctx. exact (merge_fixed_lookups x y xs ys m Hctx).
Qed.

Lemma merge_context_fiber_constants Γ x y s m mfib :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! x=Some (TBase TList) -> erase_ctx Γ !! y=Some (TBase TList) ->
  m ⊨ ctx_denote_under ∅ Γ -> res_fiber_from_projection m {[x;y]} s mfib ->
  exists xs ys, mfib ⊨ ctx_denote_under ∅ (merge_fixed_ctx x y xs ys).
Proof.
  intros HΓ Hx Hy Hctx Hfib.
  destruct (world_wf mfib) as [[t Ht] _].
  pose proof (res_fiber_from_projection_store_source _ _ _ _ _ Hfib Ht) as Htm.
  destruct (ctx_denote_under_lookup_typed ∅ Γ x _ m t HΓ Hx Hctx Htm) as [vx [Hvx Htx]].
  destruct (ctx_denote_under_lookup_typed ∅ Γ y _ m t HΓ Hy Hctx Htm) as [vy [Hvy Hty]].
  destruct (basic_typing_list_canonical_form _ Htx) as [xs ->].
  destruct (basic_typing_list_canonical_form _ Hty) as [ys ->].
  exists xs,ys. apply nat_pair_denote_intro;
    [apply merge_singleton_wf|apply const_precise_fv|apply const_precise_fv| |].
  - exact (ctx_const_bind_denote_fiber ∅ Γ x (clist xs) m mfib {[x;y]} s t HΓ Hx Hctx ltac:(set_solver) Hfib Ht Hvx).
  - exact (ctx_const_bind_denote_fiber ∅ Γ y (clist ys) m mfib {[x;y]} s t HΓ Hy Hctx ltac:(set_solver) Hfib Ht Hvy).
Qed.

Theorem merge_body_graph_context_typed Φ Γ x y : x<>y ->
  wf_ctx_under ∅ Γ ->
  erase_ctx Γ = erase_ctx (merge_fixed_ctx x y [] []) ->
  has_context_type Φ ∅ Γ (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_graph_ty IncorrectMerge.result x y).
Proof.
  intros Hxy HΓ Herase.
  destruct (merge_pair_list_lookups x y (merge_singleton_ty []) (merge_singleton_ty []) Hxy eq_refl eq_refl) as [Hx Hy].
  change (erase_ctx (merge_fixed_ctx x y [] []) !! x=Some (TBase TList)) in Hx.
  change (erase_ctx (merge_fixed_ctx x y [] []) !! y=Some (TBase TList)) in Hy.
  rewrite <- Herase in Hx,Hy.
  assert (Hxd : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hyd : y ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hwf : context_typing_wf ∅ Γ (IncorrectMerge.body (vfvar x) (vfvar y)) (merge_graph_ty IncorrectMerge.result x y)).
  { split; [exact HΓ|]. split; [apply merge_graph_wf; assumption|apply merge_body_basic; assumption]. }
  eapply CT_FiberCases with (I:=(list nat * list nat)%type) (X:={[x;y]})
    (cases:=fun p => merge_fixed_ctx x y p.1 p.2).
  - exact Hwf.
  - intros [xs ys]. rewrite Herase. reflexivity.
  - intros [xs ys]. apply merge_body_fixed_context_typed. exact Hxy.
  - apply merge_graph_joinable; assumption.
  - intros m Hctx s mfib Hfib.
    destruct (merge_context_fiber_constants Γ x y s m mfib HΓ Hx Hy Hctx Hfib) as [xs [ys Hfixed]].
    exists (xs,ys). exact Hfixed.
Qed.
