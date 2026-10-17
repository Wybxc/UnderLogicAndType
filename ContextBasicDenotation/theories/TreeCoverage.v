(** Conditional coverage for a tree constructor.  The witnesses below all
    belong to the original world.  No Cartesian-product property of world
    extension, or stability of an arbitrary arrow, is assumed. *)
From ContextBasicDenotation Require Import Notation TermSyntax TermEval.
From CoreLang Require Import InstantiationProps StrongNormalization.

Definition variable_covers_on (m : WfWorldT) (X : aset) (x : atom)
    (P : StoreT -> value -> Prop) : Prop :=
  forall σ v, (m : WorldT) σ -> P (store_restrict σ X) v ->
    exists σ', (m : WorldT) σ' /\
      store_restrict σ' X = store_restrict σ X /\ σ' !! x = Some v.

Lemma tm_eval_tree_node_vars σ xk xl xr k l rr :
  σ !! xk = Some (vconst (cnat k)) ->
  σ !! xl = Some (vconst (ctree l)) ->
  σ !! xr = Some (vconst (ctree rr)) ->
  tm_eval_in_store σ (tnode (vfvar xk) (vfvar xl) (vfvar xr))
    (vconst (ctree (tr_node k l rr))).
Proof.
  intros Hk Hl Hr.
  unfold tm_eval_in_store, expr_eval_in_store,
    lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite lstore_free_part_lift_free.
  rewrite lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite Hk, Hl, Hr.
  apply Steps_step with (e2 := tret (vconst (ctree (tr_node k l rr)))).
  - apply Step_head, HS_TreeNode. repeat constructor.
  - apply Steps_refl. repeat constructor.
Qed.

Lemma tm_total_tree_node_vars (σ : StoreT) xk xl xr k l rr :
  σ !! xk = Some (vconst (cnat k)) ->
  σ !! xl = Some (vconst (ctree l)) ->
  σ !! xr = Some (vconst (ctree rr)) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (tnode (vfvar xk) (vfvar xl) (vfvar xr))).
Proof.
  intros Hk Hl Hr.
  unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite lstore_free_part_lift_free.
  rewrite lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite Hk, Hl, Hr.
  apply Must_step.
  - eexists. apply Step_head, HS_TreeNode. repeat constructor.
  - intros e' Hstep. inversion Hstep; subst.
    match goal with H : head_step _ _ |- _ => inversion H; subst end.
    apply must_terminating_tret. constructor.
Qed.

Lemma conditional_node_coverage
    (m : WfWorldT) (S : aset) xp xk xl xr
    (P : StoreT -> nat -> Prop)
    (K : StoreT -> nat -> nat -> Prop)
    (L : StoreT -> nat -> tree -> Prop)
    (R : StoreT -> nat -> tree -> tree -> Prop)
    (Q : StoreT -> tree -> Prop) :
  variable_covers_on m S xp
    (fun s v => exists p, v = vconst (cnat p) /\ P s p) ->
  (forall σ p l, (m : World) σ -> σ !! xp = Some (vconst (cnat p)) ->
    L (store_restrict σ S) p l ->
    exists σ', (m : World) σ' /\
      store_restrict σ' (S ∪ {[xp]}) = store_restrict σ (S ∪ {[xp]}) /\
      σ' !! xl = Some (vconst (ctree l))) ->
  (forall σ p l rr, (m : World) σ ->
    σ !! xp = Some (vconst (cnat p)) -> σ !! xl = Some (vconst (ctree l)) ->
    R (store_restrict σ S) p l rr ->
    exists σ', (m : World) σ' /\
      store_restrict σ' (S ∪ {[xp;xl]}) = store_restrict σ (S ∪ {[xp;xl]}) /\
      σ' !! xr = Some (vconst (ctree rr))) ->
  (forall σ p, (m : World) σ -> σ !! xp = Some (vconst (cnat p)) ->
    exists k, σ !! xk = Some (vconst (cnat k)) /\ K (store_restrict σ S) p k) ->
  (forall s t, Q s t ->
    exists p k l rr, t = tr_node k l rr /\
      P s p /\ L s p l /\ R s p l rr /\ (forall k', K s p k' -> k' = k)) ->
  forall σ t, (m : World) σ -> Q (store_restrict σ S) t ->
    exists σ', (m : World) σ' /\ store_restrict σ' S = store_restrict σ S /\
      tm_eval_in_store σ' (tnode (vfvar xk) (vfvar xl) (vfvar xr))
        (vconst (ctree t)).
Proof.
  intros HP HL HR HK Hdecomp σ t Hσ Ht.
  destruct (Hdecomp _ _ Ht) as (p & k & l & rr & -> & Hp & Hl & Hr & Hunique).
  destruct (HP σ (vconst (cnat p)) Hσ ltac:(exists p; auto))
    as (σp & Hσp & HSp & Hxp).
  destruct (HL σp p l Hσp Hxp ltac:(rewrite HSp; exact Hl))
    as (σl & Hσl & HSlp & Hxl).
  assert (HSl : store_restrict σl S = store_restrict σ S).
  { transitivity (store_restrict σp S); [|exact HSp].
    eapply storeA_restrict_eq_mono; [|exact HSlp]. set_solver. }
  assert (Hxpl : σl !! xp = Some (vconst (cnat p))).
  { eapply storeA_restrict_lookup_transport;
      [|symmetry; exact HSlp|exact Hxp]. set_solver. }
  destruct (HR σl p l rr Hσl Hxpl Hxl ltac:(rewrite HSl; exact Hr))
    as (σr & Hσr & HSrl & Hxr).
  assert (HSr : store_restrict σr S = store_restrict σ S).
  { transitivity (store_restrict σl S); [|exact HSl].
    eapply storeA_restrict_eq_mono; [|exact HSrl]. set_solver. }
  assert (Hxpr : σr !! xp = Some (vconst (cnat p))).
  { eapply storeA_restrict_lookup_transport;
      [|symmetry; exact HSrl|exact Hxpl]. set_solver. }
  assert (Hxlr : σr !! xl = Some (vconst (ctree l))).
  { eapply storeA_restrict_lookup_transport;
      [|symmetry; exact HSrl|exact Hxl]. set_solver. }
  destruct (HK σr p Hσr Hxpr) as [k' [Hk' HK']].
  rewrite HSr in HK'. specialize (Hunique k' HK'). subst k'.
  exists σr. split; [exact Hσr|]. split; [exact HSr|].
  apply tm_eval_tree_node_vars; assumption.
Qed.
