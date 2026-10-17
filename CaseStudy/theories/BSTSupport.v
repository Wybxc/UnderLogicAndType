(** Store interpretation of the original BST qualifier, so support changes
    can use the fixed-parameter bridge without changing the specification. *)
From CaseStudy Require Import CaseTypes BSTGenerator BSTNodeTypes.
From Denotation Require Import Notation Context TypeDenote ResultQualifier QualifierStore.
From ContextTyping Require Import Typing FixedParameters.

Definition bst_lookup_result u v (s : StoreT) w : Prop :=
  exists n a t, s !! u = Some (vconst (cnat n)) /\
    s !! v = Some (vconst (cnat a)) /\
    w = vconst (ctree t) /\ bst_spec n a t.

Lemma q_bst_free_param u v :
  q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0) =
    param_result_qual TTree {[u;v]} (bst_lookup_result u v).
Proof.
  apply qual_ext.
  - cbn [q_tree_bst_range param_result_qual qual_lvars lvar_value_keys].
    assert (H : lvars_of_atoms {[u;v]} = {[LVFree u;LVFree v]}).
    { apply set_eq. intros z. unfold lvars_of_atoms. rewrite elem_of_map. set_solver. }
    rewrite H. set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [q_tree_bst_range param_result_qual qual_prop qual_lvars lvar_value_keys
      denote_lvar_value lso_store storeAO_store].
    rewrite Hs. unfold bst_lookup_result, lstore_free_part.
    rewrite !lstore_to_store_lookup.
    split.
    + intros [n [a [t [Hn [Ha [Ht Hbst]]]]]].
      exists (vconst (ctree t)). split; [exact Ht|].
      split; [apply BVT_Const|]. exists n, a, t. auto.
    + intros [w [Hw [_ [n [a [t [Hn [Ha [-> Hbst]]]]]]]]].
      exists n, a, t. auto.
Qed.

Lemma q_bst_free_dom u v :
  qual_dom (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)) = {[u;v]}.
Proof. rewrite q_bst_free_param. apply param_result_qual_dom. Qed.

Lemma q_bst_free_open_store u v y σ :
  y ∉ ({[u;v]} : aset) ->
  qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))) σ <->
  ({[u;v]} : aset) ⊆ dom (σ : StoreT) /\
  exists n a t, σ !! u = Some (vconst (cnat n)) /\
    σ !! v = Some (vconst (cnat a)) /\
    σ !! y = Some (vconst (ctree t)) /\ bst_spec n a t.
Proof.
  intros Hy. rewrite q_bst_free_param, typed_param_result_qual_open_store by exact Hy.
  unfold bst_lookup_result. split.
  - intros [Hscope [w [Hwy [_ [n [a [t [Hn [Ha [-> Hbst]]]]]]]]]].
    rewrite !store_restrict_lookup_at in Hn, Ha by set_solver.
    split; [exact Hscope|]. exists n, a, t. auto.
  - intros [Hscope [n [a [t [Hn [Ha [Hty Hbst]]]]]]].
    split; [exact Hscope|]. exists (vconst (ctree t)). split; [exact Hty|].
    split; [apply BVT_Const|]. exists n, a, t.
    rewrite !store_restrict_lookup_at by set_solver. auto.
Qed.

Lemma q_bst_const_param n a :
  q_tree_bst_range (vconst (cnat n)) (vconst (cnat a)) (vbvar 0) =
    param_result_qual TTree ∅ (fun _ w => exists t, w = vconst (ctree t) /\ bst_spec n a t).
Proof.
  apply qual_ext.
  - cbn [q_tree_bst_range param_result_qual qual_lvars lvar_value_keys].
    unfold lvars_of_atoms. rewrite set_map_empty. set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [q_tree_bst_range param_result_qual qual_prop qual_lvars lvar_value_keys
      denote_lvar_value lso_store storeAO_store].
    rewrite Hs. split.
    + intros [n' [a' [t [Hn [Ha [Ht Hbst]]]]]].
      inversion Hn; inversion Ha; subst n' a'.
      exists (vconst (ctree t)). split; [exact Ht|].
      split; [apply BVT_Const|]. exists t. auto.
    + intros [w [Hw [_ [t [-> Hbst]]]]].
      exists n, a, t. auto.
Qed.

Lemma q_bst_const_open_store n a y σ :
  qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (q_tree_bst_range (vconst (cnat n)) (vconst (cnat a)) (vbvar 0)))) σ <->
  exists t, σ !! y = Some (vconst (ctree t)) /\ bst_spec n a t.
Proof.
  rewrite q_bst_const_param, typed_param_result_qual_open_store by set_solver.
  split.
  - intros [_ [w [Hwy [_ [t [-> Hbst]]]]]]. exists t. auto.
  - intros [t [Hty Hbst]]. split; [set_solver|].
    exists (vconst (ctree t)). split; [exact Hty|].
    split; [apply BVT_Const|]. exists t. auto.
Qed.

Lemma q_bst_free_wf d D u v :
  u ∈ D -> v ∈ D ->
  wf_context_ty_at d D (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof. intros Hu Hv. rewrite q_bst_free_param. apply param_result_qual_wf. set_solver. Qed.

Lemma q_bst_const_wf d D n a :
  wf_context_ty_at d D (CTUnder TTree
    (q_tree_bst_range (vconst (cnat n)) (vconst (cnat a)) (vbvar 0))).
Proof. rewrite q_bst_const_param. apply param_result_qual_wf. set_solver. Qed.

Lemma q_bst_fixed_open_equiv n a u v y τ :
  y ∉ ({[u;v]} : aset) ->
  τ !! u = Some (vconst (cnat n)) -> τ !! v = Some (vconst (cnat a)) ->
  (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
     (q_tree_bst_range (vconst (cnat n)) (vconst (cnat a)) (vbvar 0)))) τ <->
   qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
     (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))) τ).
Proof.
  intros Hy Hu Hv. rewrite q_bst_const_open_store, q_bst_free_open_store by exact Hy.
  split.
  - intros [t [Ht Hbst]]. split.
    + assert (HuD : u ∈ dom (τ : gmap atom value)) by (eapply elem_of_dom_2; exact Hu).
      assert (HvD : v ∈ dom (τ : gmap atom value)) by (eapply elem_of_dom_2; exact Hv).
      clear -HuD HvD. set_solver.
    + exists n, a, t. auto.
  - intros [_ [n' [a' [t [Hu' [Hv' [Ht Hbst]]]]]]].
    rewrite Hu in Hu'. rewrite Hv in Hv'. inversion Hu'; inversion Hv'; subst n' a'.
    exists t. auto.
Qed.

Lemma q_bst_constants_subtype Σ Γ n a u v :
  wf_ctx_under Σ Γ -> u ∈ dom (erase_ctx Γ) -> v ∈ dom (erase_ctx Γ) ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! u = Some (vconst (cnat n)) /\ σ !! v = Some (vconst (cnat a))) ->
  sub_type_under Σ Γ
    (CTUnder TTree (q_tree_bst_range (vconst (cnat n)) (vconst (cnat a)) (vbvar 0)))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros HΓ Hu Hv Hlook. eapply sub_type_under_worldwise_fixed with (F:={[u;v]}).
  - exact HΓ.
  - apply q_bst_const_wf.
  - apply q_bst_free_wf; assumption.
  - rewrite q_bst_const_param, param_result_qual_dom. apply empty_subseteq.
  - rewrite q_bst_free_dom. reflexivity.
  - intros m Hctx. destruct (world_wf m) as [[σ0 Hσ0] _].
    exists (store_restrict σ0 {[u;v]}). split.
    + intros σ Hσ. apply store_restrict_eq_on. intros x Hx.
      assert (x = u \/ x = v) by (clear -Hx; set_solver). destruct H as [-> | ->].
      * exact (eq_trans (proj1 (Hlook m σ Hctx Hσ)) (eq_sym (proj1 (Hlook m σ0 Hctx Hσ0)))).
      * exact (eq_trans (proj2 (Hlook m σ Hctx Hσ)) (eq_sym (proj2 (Hlook m σ0 Hctx Hσ0)))).
    + intros y τ Hy Hτ. apply q_bst_fixed_open_equiv; [exact Hy| |].
      * eapply (store_restrict_eq_lookup σ0 τ {[u;v]} u (vconst (cnat n)));
          [clear; set_solver|exact (eq_sym Hτ)|exact (proj1 (Hlook m σ0 Hctx Hσ0))].
      * eapply (store_restrict_eq_lookup σ0 τ {[u;v]} v (vconst (cnat a)));
          [clear; set_solver|exact (eq_sym Hτ)|exact (proj2 (Hlook m σ0 Hctx Hσ0))].
Qed.

Lemma bst_result_fixed_open_equiv n a u v y (τ : StoreT) :
  y ∉ ({[u;v]} : aset) ->
  τ !! u = Some (vnat n) -> τ !! v = Some (vnat a) ->
  (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
     (bst_result_qual {[u;v]} n a))) τ <->
   qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
     (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))) τ).
Proof.
  intros Hy Hu Hv. rewrite q_bst_free_open_store by exact Hy.
  unfold bst_result_qual. rewrite typed_param_result_qual_open_store by exact Hy.
  split.
  - intros [Hscope [w [Hwy [_ [t [-> Hbst]]]]]].
    split; [exact Hscope|]. exists n,a,t. auto.
  - intros [Hscope [n' [a' [t [Hu' [Hv' [Ht Hbst]]]]]]].
    assert (Hn : n'=n) by (rewrite Hu in Hu'; now inversion Hu').
    assert (Ha : a'=a) by (rewrite Hv in Hv'; now inversion Hv').
    subst n' a'. split; [exact Hscope|]. exists (vconst (ctree t)).
    split; [exact Ht|]. split; [apply BVT_Const|]. exists t. auto.
Qed.

Lemma bst_result_to_free_subtype Σ Γ n a u v :
  wf_ctx_under Σ Γ -> u ∈ dom (erase_ctx Γ) -> v ∈ dom (erase_ctx Γ) ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a)) ->
  sub_type_under Σ Γ (CTUnder TTree (bst_result_qual {[u;v]} n a))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros HΓ Hu Hv Hlook. eapply sub_type_under_worldwise_fixed with (F:={[u;v]}).
  - exact HΓ.
  - unfold bst_result_qual. apply param_result_qual_wf. clear -Hu Hv. set_solver.
  - apply q_bst_free_wf; assumption.
  - unfold bst_result_qual. rewrite param_result_qual_dom. reflexivity.
  - rewrite q_bst_free_dom. reflexivity.
  - intros m Hctx. destruct (world_wf m) as [[σ0 Hσ0] _].
    exists (store_restrict σ0 {[u;v]}). split.
    + intros σ Hσ. apply store_restrict_eq_on. intros x Hx.
      assert (x=u \/ x=v) by (clear -Hx; set_solver). destruct H as [-> | ->].
      * exact (eq_trans (proj1 (Hlook m σ Hctx Hσ)) (eq_sym (proj1 (Hlook m σ0 Hctx Hσ0)))).
      * exact (eq_trans (proj2 (Hlook m σ Hctx Hσ)) (eq_sym (proj2 (Hlook m σ0 Hctx Hσ0)))).
    + intros y τ Hy Hτ. apply bst_result_fixed_open_equiv; [exact Hy| |].
      * eapply (store_restrict_eq_lookup σ0 τ {[u;v]} u (vnat n));
          [clear; set_solver|exact (eq_sym Hτ)|exact (proj1 (Hlook m σ0 Hctx Hσ0))].
      * eapply (store_restrict_eq_lookup σ0 τ {[u;v]} v (vnat a));
          [clear; set_solver|exact (eq_sym Hτ)|exact (proj2 (Hlook m σ0 Hctx Hσ0))].
Qed.
