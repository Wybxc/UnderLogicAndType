(** Structural facts used by the context-typing proof of the generator. *)
From CaseStudy Require Import CaseTypes BSTGenerator.
From Stdlib Require Import Lia PeanoNat.
Open Scope nat_scope.

Lemma bst_between_member lo hi t k :
  bst_between lo hi t -> tree_mem k t -> lo <= k < hi.
Proof.
  revert lo hi. induction t as [|r l IHl rr IHrr];
    intros lo hi Hbst Hmem; cbn in *; [contradiction|].
  destruct Hbst as [Hr [Hl Hrr]].
  destruct Hmem as [->|[Hmem|Hmem]]; [exact Hr| |].
  - specialize (IHl _ _ Hl Hmem). lia.
  - specialize (IHrr _ _ Hrr Hmem). lia.
Qed.

Lemma bst_between_bounds lo hi lo' hi' t :
  lo' <= lo -> hi <= hi' ->
  bst_between lo hi t -> bst_between lo' hi' t.
Proof.
  revert lo hi lo' hi'. induction t as [|r l IHl rr IHrr];
    intros lo hi lo' hi' Hlo Hhi Hbst; cbn in *; [exact I|].
  destruct Hbst as [Hr [Hl Hrr]].
  repeat split; try lia.
  - exact (IHl _ _ _ _ Hlo (Nat.le_refl _) Hl).
  - exact (IHrr _ _ _ _ (Nat.le_refl _) Hhi Hrr).
Qed.

Lemma bst_spec_leaf n lo : bst_spec n lo tr_leaf <-> n = 0.
Proof.
  unfold bst_spec. cbn. split.
  - intros [_ H]. specialize (H (S lo)). lia.
  - intros ->. split; [exact I|]. intros k. lia.
Qed.

Lemma bst_spec_zero lo t : bst_spec 0 lo t <-> t = tr_leaf.
Proof.
  destruct t as [|r l rr].
  - rewrite bst_spec_leaf. tauto.
  - unfold bst_spec. cbn. split; [intros [[Hr _] _]; lia|discriminate].
Qed.

Lemma bst_spec_node n lo k l rr :
  bst_spec n lo (tr_node k l rr) <->
  exists p, 1 <= p <= n /\ k = lo + p /\
    bst_spec (p - 1) lo l /\ bst_spec (n - p) (lo + p) rr.
Proof.
  split.
  - intros [[Hk [Hl Hrr]] Hmem].
    exists (k - lo).
    assert (Hp : 1 <= k - lo <= n) by lia.
    assert (Ek : k = lo + (k - lo)) by lia.
    split; [exact Hp|]. split; [exact Ek|].
    assert (El : S (lo + (k - lo - 1)) = k) by lia.
    assert (Er : lo + (k - lo) + (n - (k - lo)) = lo + n) by lia.
    split; split.
    + rewrite El. exact Hl.
    + intros j. split.
      * intros Hj. pose proof (bst_between_member _ _ _ _ Hl Hj). lia.
      * intros Hj.
        assert (Hjwhole : tree_mem j (tr_node k l rr))
          by (apply (proj2 (Hmem j)); lia).
        cbn in Hjwhole. destruct Hjwhole as [Heq|[Hleft|Hright]].
        -- lia.
        -- exact Hleft.
        -- pose proof (bst_between_member _ _ _ _ Hrr Hright). lia.
    + rewrite Er, <- Ek. exact Hrr.
    + intros j. split.
      * intros Hj. pose proof (bst_between_member _ _ _ _ Hrr Hj). lia.
      * intros Hj.
        assert (Hjwhole : tree_mem j (tr_node k l rr))
          by (apply (proj2 (Hmem j)); lia).
        cbn in Hjwhole. destruct Hjwhole as [Heq|[Hleft|Hright]].
        -- lia.
        -- pose proof (bst_between_member _ _ _ _ Hl Hleft). lia.
        -- exact Hright.
  - intros [p [Hp [-> [[Hl Hml] [Hrr Hmr]]]]].
    assert (El : S (lo + (p - 1)) = lo + p) by lia.
    assert (Er : lo + p + (n - p) = lo + n) by lia.
    split.
    + cbn. rewrite El in Hl. rewrite Er in Hrr.
      repeat split; try lia; assumption.
    + intros j. cbn. rewrite Hml, Hmr. lia.
Qed.

Lemma bst_spec_positive_decompose n lo t :
  0 < n -> bst_spec n lo t ->
  exists p l rr, 1 <= p <= n /\
    t = tr_node (lo + p) l rr /\
    bst_spec (p - 1) lo l /\ bst_spec (n - p) (lo + p) rr.
Proof.
  intros Hn Ht. destruct t as [|k l rr].
  - apply bst_spec_leaf in Ht. lia.
  - apply bst_spec_node in Ht as [p [Hp [Hk [Hl Hrr]]]].
    exists p, l, rr. subst k. split; [exact Hp|].
    split; [reflexivity|]. split; assumption.
Qed.

Lemma bst_pivot_sizes_decrease n p :
  1 <= p <= n -> p - 1 < n /\ n - p < n.
Proof. lia. Qed.

Lemma bst_spec_inhabited n lo : exists t, bst_spec n lo t.
Proof.
  revert lo. induction n as [|n IH]; intros lo.
  - exists tr_leaf. apply bst_spec_leaf. reflexivity.
  - destruct (IH (lo + 1)) as [rr Hrr].
    exists (tr_node (lo + 1) tr_leaf rr).
    apply bst_spec_node. exists 1.
    split; [lia|]. split; [reflexivity|]. split.
    + apply bst_spec_leaf. reflexivity.
    + replace (S n - 1) with n by lia. exact Hrr.
Qed.
