(** Derived conversion rules for deterministic administrative reductions.
    A recursive call is typed before its surrounding finite reduction prefix. *)
From CoreLang Require Import InstantiationProps OperationalProps StrongNormalization.
From Denotation Require Import Context TypeEquivTermBase.
From ContextTyping Require Import Typing TypingRegular.

Lemma instantiate_closed_tm σ e :
  fv_tm e = ∅ ->
  lstore_instantiate_tm (lstore_lift_free σ) e = e.
Proof.
  intros Hfv. unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite lstore_free_part_lift_free.
  rewrite lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  rewrite <- (lstore_instantiate_tm_split_restrict_fv 0 σ ∅ e ∅) by set_solver.
  rewrite storeA_restrict_empty_set.
  rewrite lstore_instantiate_tm_split_empty_bound.
  - rewrite subst_map_tm_eq_msubst, msubst_empty. reflexivity.
  - apply map_Forall_lookup_2. intros x v H. rewrite lookup_empty in H. discriminate.
Qed.

Lemma deterministic_step_equivalence e e' :
  step e e' ->
  (forall z, step e z -> z = e') ->
  (forall v, e →* tret v <-> e' →* tret v) /\
  (must_terminating e <-> must_terminating e').
Proof.
  intros Hstep Hdet. split.
  - intros v. split.
    + intros Hrun. inversion Hrun; subst.
      * exfalso. eapply val_no_step; exact Hstep.
      * match goal with Hs : step e ?z |- _ =>
          rewrite (Hdet z Hs) in * end. assumption.
    + intros Hrun. econstructor; eauto.
  - split.
    + intros H. eapply must_terminating_step_inv; eauto.
    + intros H. apply Must_step.
      * exists e'. exact Hstep.
      * intros z Hz. rewrite (Hdet z Hz). exact H.
Qed.

Lemma typing_closed_deterministic_step Φ Σ Γ e e' τ :
  context_typing_wf Σ Γ e τ ->
  (step e e' /\ (forall z, step e z -> z = e')) ->
  fv_tm e = ∅ -> fv_tm e' = ∅ ->
  has_context_type Φ Σ Γ e' τ ->
  has_context_type Φ Σ Γ e τ.
Proof.
  intros Hwf [Hstep Hdet] He He' Hty.
  destruct (deterministic_step_equivalence e e' Hstep Hdet) as [Hrun Htotal].
  eapply CT_Conv; [exact Hwf|exact Hty|].
  intros m _. split.
  - intros σ v _. unfold tm_eval_in_store, expr_eval_in_store.
    rewrite !instantiate_closed_tm by assumption. symmetry. apply Hrun.
  - intros σ _. rewrite !instantiate_closed_tm by assumption.
    symmetry. exact Htotal.
Qed.
