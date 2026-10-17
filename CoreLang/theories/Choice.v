(** Angelic choice built from the existing boolean generator. *)
From CoreLang Require Import Sugar StrongNormalization Instantiation InstantiationProps OperationalProps.

Definition choose_tm (left right : tm) : tm :=
  tlete (tprim op_boolGen (vconst cunit))
    (tmatch (vbvar 0) (tm_shift 0 left) (tm_shift 0 right)).

Lemma choose_body_lc left right :
  lc_tm left -> lc_tm right -> body_tm (tmatch (vbvar 0) left right).
Proof.
  intros Hl Hr. exists ∅. intros x _.
  change (lc_tm (open_tm 0 (vfvar x) (tmatch (vbvar 0) left right))).
  cbn [open_tm open_value].
  rewrite !open_rec_lc_tm by assumption. constructor; auto; constructor.
Qed.

Lemma choose_body_open left right v :
  lc_tm left -> lc_tm right ->
  open_tm 0 v (tmatch (vbvar 0) left right) = tmatch v left right.
Proof.
  intros Hl Hr. cbn [open_tm open_value].
  rewrite !open_rec_lc_tm by assumption. reflexivity.
Qed.

Lemma choose_tm_lc left right :
  lc_tm left -> lc_tm right -> lc_tm (choose_tm left right).
Proof.
  intros Hl Hr. unfold choose_tm. rewrite !tm_shift_lc_id by assumption.
  apply lc_lete_iff_body. split; [repeat constructor|].
  apply choose_body_lc; assumption.
Qed.

Lemma msubst_choose_tm σ left right :
  lc_env σ -> lc_tm left -> lc_tm right ->
  m{σ} (choose_tm left right) = choose_tm (m{σ} left) (m{σ} right).
Proof.
  intros Hσ Hl Hr. unfold choose_tm.
  rewrite !tm_shift_lc_id by (first [assumption|apply msubst_lc; assumption]).
  rewrite msubst_lete, msubst_tprim, msubst_tmatch.
  rewrite (msubst_fresh σ (vconst cunit)) by
    (change (dom σ ∩ ∅ = (∅ : aset)); set_solver).
  rewrite (msubst_fresh σ (vbvar 0)) by
    (change (dom σ ∩ ∅ = (∅ : aset)); set_solver).
  reflexivity.
Qed.

Lemma choose_tm_results left right v :
  lc_tm left -> lc_tm right ->
  (choose_tm left right →* tret v <-> left →* tret v \/ right →* tret v).
Proof.
  intros Hl Hr. unfold choose_tm. rewrite !tm_shift_lc_id by assumption.
  rewrite reduction_lete_iff by (apply choose_body_lc; assumption).
  split.
  - intros [vx [Hgen Hbranch]].
    apply reduction_prim_const in Hgen as [c [Hc ->]].
    inversion Hc; subst.
    rewrite choose_body_open in Hbranch by assumption.
    destruct b.
    + left. apply reduction_match_true in Hbranch. exact Hbranch.
    + right. apply reduction_match_false in Hbranch. exact Hbranch.
  - intros [Hleft|Hright].
    + exists (vconst (cbool true)). split.
      * apply reduction_prim_intro. constructor.
      * rewrite choose_body_open by assumption.
        apply reduction_match_true_intro; assumption.
    + exists (vconst (cbool false)). split.
      * apply reduction_prim_intro. constructor.
      * rewrite choose_body_open by assumption.
        apply reduction_match_false_intro; assumption.
Qed.

Lemma choose_tm_must_terminate left right :
  lc_tm left -> lc_tm right ->
  (must_terminating (choose_tm left right) <->
    must_terminating left /\ must_terminating right).
Proof.
  intros Hl Hr. unfold choose_tm. rewrite !tm_shift_lc_id by assumption.
  assert (Hbody : body_tm (tmatch (vbvar 0) left right))
    by (apply choose_body_lc; assumption).
  split.
  - intros Htotal. split.
    + pose proof (must_terminating_tlete_elim_body _ _
        (vconst (cbool true)) Hbody ltac:(apply reduction_prim_intro; constructor)
        Htotal) as Hbranch.
      rewrite choose_body_open in Hbranch by assumption.
      apply (proj1 (must_terminating_match_true_equiv left right
        ltac:(constructor; auto; constructor))). exact Hbranch.
    + pose proof (must_terminating_tlete_elim_body _ _
        (vconst (cbool false)) Hbody ltac:(apply reduction_prim_intro; constructor)
        Htotal) as Hbranch.
      rewrite choose_body_open in Hbranch by assumption.
      apply (proj1 (must_terminating_match_false_equiv left right
        ltac:(constructor; auto; constructor))). exact Hbranch.
  - intros [Hleft Hright]. apply must_terminating_tlete_intro; [exact Hbody| |].
    + apply must_terminating_tprim_const; [repeat constructor|].
      exists (cbool true). constructor.
    + intros vx Hgen. apply reduction_prim_const in Hgen as [c [Hc ->]].
      inversion Hc; subst. rewrite choose_body_open by assumption.
      destruct b.
      * apply (proj2 (must_terminating_match_true_equiv left right
          ltac:(constructor; auto; constructor))). exact Hleft.
      * apply (proj2 (must_terminating_match_false_equiv left right
          ltac:(constructor; auto; constructor))). exact Hright.
Qed.
