(** The original recursive-call specification is retained.  It is converted
    to conditional left/right coverage only after the case fixes support. *)
From CaseStudy Require Import BSTGenerator BSTNodeTypes BSTSupport NatArithmetic.
From Denotation Require Import Context ResultQualifier QualifierStore.
From ContextTyping Require Import Typing FixedParameters OverConsequence.

Lemma store_nat_lookup_unique (σ : StoreT) x n k :
  σ !! x = Some (vnat n) -> σ !! x = Some (vnat k) -> n=k.
Proof. intros Hn Hk. pose proof (eq_trans (eq_sym Hn) Hk) as H. now inversion H. Qed.

Lemma store_restrict_eq_scope (σ τ : StoreT) F :
  F ⊆ dom (σ : StoreT) -> store_restrict σ F = store_restrict τ F ->
  F ⊆ dom (τ : StoreT).
Proof.
  intros Hscope Heq x Hx.
  change (F ⊆ dom (σ : gmap atom value)) in Hscope.
  change (x ∈ dom (τ : gmap atom value)).
  destruct (proj1 (elem_of_dom (σ : gmap atom value) x) (Hscope x Hx)) as [v Hv].
  apply elem_of_dom. exists v. exact (store_restrict_eq_lookup σ τ F x v Hx Heq Hv).
Qed.

Lemma bst_left_fixed_open_equiv S xp sz lo n a p y (τ : StoreT) :
  y ∉ S ∪ {[xp;sz;lo]} -> (S ∪ {[xp;sz;lo]}) ⊆ dom (τ : StoreT) ->
  1 <= p <= n -> τ !! xp = Some (vnat p) ->
  τ !! sz = Some (vnat (p-1)) -> τ !! lo = Some (vnat a) ->
  (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (q_tree_bst_range (vfvar sz) (vfvar lo) (vbvar 0)))) τ <->
   qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (bst_left_qual S xp n a))) τ).
Proof.
  intros Hy Hscope Hp Hxp Hsz Hlo.
  rewrite q_bst_free_open_store by (clear -Hy; set_solver).
  unfold bst_left_qual. rewrite typed_param_result_qual_open_store by (clear -Hy; set_solver).
  split.
  - intros [_ [n' [a' [t [Hsz' [Hlo' [Hty Hbst]]]]]]].
    assert (n'=p-1) by (eapply store_nat_lookup_unique; [exact Hsz'|exact Hsz]).
    assert (a'=a) by (eapply store_nat_lookup_unique; [exact Hlo'|exact Hlo]).
    subst n' a'. split; [clear -Hscope; set_solver|].
    exists (vconst (ctree t)). split; [exact Hty|].
    split; [apply BVT_Const|]. exists p,t. split.
    + rewrite store_restrict_lookup_at by set_solver. exact Hxp.
    + auto.
  - intros [_ [w [Hyw [_ [p' [t [Hxp' [-> [Hp' Hbst]]]]]]]]].
    rewrite store_restrict_lookup_at in Hxp' by set_solver.
    assert (p'=p) by (eapply store_nat_lookup_unique; [exact Hxp'|exact Hxp]).
    subst p'. split; [clear -Hscope; set_solver|].
    exists (p-1),a,t. auto.
Qed.

Lemma bst_right_fixed_open_equiv S xp xl sz lo n a p y (τ : StoreT) :
  y ∉ S ∪ {[xp;xl;sz;lo]} -> (S ∪ {[xp;xl;sz;lo]}) ⊆ dom (τ : StoreT) ->
  1 <= p <= n -> τ !! xp = Some (vnat p) ->
  τ !! sz = Some (vnat (n-p)) -> τ !! lo = Some (vnat (a+p)) ->
  (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (q_tree_bst_range (vfvar sz) (vfvar lo) (vbvar 0)))) τ <->
   qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree
    (bst_right_qual S xp xl n a))) τ).
Proof.
  intros Hy Hscope Hp Hxp Hsz Hlo.
  rewrite q_bst_free_open_store by (clear -Hy; set_solver).
  unfold bst_right_qual. rewrite typed_param_result_qual_open_store by (clear -Hy; set_solver).
  split.
  - intros [_ [n' [a' [t [Hsz' [Hlo' [Hty Hbst]]]]]]].
    assert (n'=n-p) by (eapply store_nat_lookup_unique; [exact Hsz'|exact Hsz]).
    assert (a'=a+p) by (eapply store_nat_lookup_unique; [exact Hlo'|exact Hlo]).
    subst n' a'. split; [clear -Hscope; set_solver|].
    exists (vconst (ctree t)). split; [exact Hty|].
    split; [apply BVT_Const|]. exists p,t. split.
    + rewrite store_restrict_lookup_at by set_solver. exact Hxp.
    + auto.
  - intros [_ [w [Hyw [_ [p' [t [Hxp' [-> [Hp' Hbst]]]]]]]]].
    rewrite store_restrict_lookup_at in Hxp' by set_solver.
    assert (p'=p) by (eapply store_nat_lookup_unique; [exact Hxp'|exact Hxp]).
    subst p'. split; [clear -Hscope; set_solver|].
    exists (n-p),(a+p),t. auto.
Qed.

Lemma bst_left_fixed_call_subtype Σ Γ S xp sz lo n a p :
  wf_ctx_under Σ Γ -> S ∪ {[xp;sz;lo]} ⊆ dom (erase_ctx Γ) -> 1 <= p <= n ->
  (forall m, m ⊨ ctx_denote_under Σ Γ -> forall σ τ,
    (m : WorldT) σ -> (m : WorldT) τ ->
    store_restrict σ (S ∪ {[xp;sz;lo]}) = store_restrict τ (S ∪ {[xp;sz;lo]})) ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! xp = Some (vnat p) /\ σ !! sz = Some (vnat (p-1)) /\
    σ !! lo = Some (vnat a)) ->
  sub_type_under Σ Γ
    (CTUnder TTree (q_tree_bst_range (vfvar sz) (vfvar lo) (vbvar 0)))
    (CTUnder TTree (bst_left_qual S xp n a)).
Proof.
  intros HΓ HF Hp Hfixed Hlook.
  eapply sub_type_under_worldwise_fixed with (F:=S ∪ {[xp;sz;lo]}).
  - exact HΓ.
  - apply q_bst_free_wf; clear -HF; set_solver.
  - unfold bst_left_qual. apply param_result_qual_wf. clear -HF. set_solver.
  - rewrite q_bst_free_dom. set_solver.
  - unfold bst_left_qual. rewrite param_result_qual_dom. set_solver.
  - intros m Hctx. destruct (world_wf m) as [[σ Hσ] _].
    exists (store_restrict σ (S ∪ {[xp;sz;lo]})). split.
    + intros τ Hτ. exact (Hfixed m Hctx τ σ Hτ Hσ).
    + intros y τ Hy Hτ.
      destruct (Hlook m σ Hctx Hσ) as [Hxp [Hsz Hlo]].
      apply (bst_left_fixed_open_equiv S xp sz lo n a p y τ); [exact Hy| |exact Hp| | |].
      * eapply store_restrict_eq_scope; [|exact (eq_sym Hτ)].
        etransitivity; [exact HF|exact (ctx_denote_under_store_scope Σ Γ m σ Hctx Hσ)].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;sz;lo]}) xp);
          [set_solver|exact (eq_sym Hτ)|exact Hxp].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;sz;lo]}) sz);
          [set_solver|exact (eq_sym Hτ)|exact Hsz].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;sz;lo]}) lo);
          [set_solver|exact (eq_sym Hτ)|exact Hlo].
Qed.

Lemma bst_right_fixed_call_subtype Σ Γ S xp xl sz lo n a p :
  wf_ctx_under Σ Γ -> S ∪ {[xp;xl;sz;lo]} ⊆ dom (erase_ctx Γ) -> 1 <= p <= n ->
  (forall m, m ⊨ ctx_denote_under Σ Γ -> forall σ τ,
    (m : WorldT) σ -> (m : WorldT) τ ->
    store_restrict σ (S ∪ {[xp;xl;sz;lo]}) = store_restrict τ (S ∪ {[xp;xl;sz;lo]})) ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! xp = Some (vnat p) /\ σ !! sz = Some (vnat (n-p)) /\
    σ !! lo = Some (vnat (a+p))) ->
  sub_type_under Σ Γ
    (CTUnder TTree (q_tree_bst_range (vfvar sz) (vfvar lo) (vbvar 0)))
    (CTUnder TTree (bst_right_qual S xp xl n a)).
Proof.
  intros HΓ HF Hp Hfixed Hlook.
  eapply sub_type_under_worldwise_fixed with (F:=S ∪ {[xp;xl;sz;lo]}).
  - exact HΓ.
  - apply q_bst_free_wf; clear -HF; set_solver.
  - unfold bst_right_qual. apply param_result_qual_wf. clear -HF. set_solver.
  - rewrite q_bst_free_dom. set_solver.
  - unfold bst_right_qual. rewrite param_result_qual_dom. set_solver.
  - intros m Hctx. destruct (world_wf m) as [[σ Hσ] _].
    exists (store_restrict σ (S ∪ {[xp;xl;sz;lo]})). split.
    + intros τ Hτ. exact (Hfixed m Hctx τ σ Hτ Hσ).
    + intros y τ Hy Hτ.
      destruct (Hlook m σ Hctx Hσ) as [Hxp [Hsz Hlo]].
      apply (bst_right_fixed_open_equiv S xp xl sz lo n a p y τ); [exact Hy| |exact Hp| | |].
      * eapply store_restrict_eq_scope; [|exact (eq_sym Hτ)].
        etransitivity; [exact HF|exact (ctx_denote_under_store_scope Σ Γ m σ Hctx Hσ)].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;xl;sz;lo]}) xp);
          [set_solver|exact (eq_sym Hτ)|exact Hxp].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;xl;sz;lo]}) sz);
          [set_solver|exact (eq_sym Hτ)|exact Hsz].
      * eapply (store_restrict_eq_lookup σ τ (S ∪ {[xp;xl;sz;lo]}) lo);
          [set_solver|exact (eq_sym Hτ)|exact Hlo].
Qed.
