(** Finite traces from revised p.25: a conjunction of input implications. *)
From CaseStudy Require Import MergeGraph.
From Denotation Require Import Context ConstDenote ConstDenoteBase TypeEquiv TypeEquivCore
  TypeEquivTermBase TypeEquivBody TypeEquivFiberBaseCore BaseIntro.
From Stdlib Require Import List.
Import ListNotations.
Definition merge_trace_relation (xs ys zs : list nat) : Prop :=
  (xs=[] /\ ys=[] -> zs=[]) /\
  (xs=[2] /\ ys=[4] -> zs=[2;4]) /\
  (xs=[1;2] /\ ys=[3;4] -> zs=[1;3;2;4]).
Lemma merge_result_trace xs ys :
  merge_trace_relation xs ys (IncorrectMerge.result xs ys).
Proof. unfold merge_trace_relation. repeat split; intros [-> ->]; reflexivity. Qed.
Definition q_merge_relation (R : list nat -> list nat -> list nat -> Prop)
  (u v w : logic_var) : type_qualifier :=
  tqual ({[u]} ∪ {[v]} ∪ {[w]})
    (fun s => exists xs ys zs,
      lso_store s !! u = Some (IncorrectMerge.vlist xs) /\
      lso_store s !! v = Some (IncorrectMerge.vlist ys) /\
      lso_store s !! w = Some (IncorrectMerge.vlist zs) /\ R xs ys zs).
Lemma q_merge_relation_open R u v w j z :
  qual_open_atom j z (q_merge_relation R u v w) =
  q_merge_relation R (swap (LVBound j) (LVFree z) u)
    (swap (LVBound j) (LVFree z) v) (swap (LVBound j) (LVFree z) w).
Proof.
  apply qual_ext.
  - cbn [qual_open_atom q_merge_relation qual_lvars].
    rewrite !set_swap_union, !set_swap_singleton. reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_open_atom q_merge_relation qual_prop qual_lvars].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value.
    setoid_rewrite Hs. reflexivity.
Qed.

Lemma q_merge_relation_typed R u v :
  typed_result_qual TList (q_merge_relation R u v (LVBound 0)) =
  q_merge_relation R u v (LVBound 0).
Proof.
  apply qual_ext.
  - cbn [typed_result_qual q_merge_relation qual_lvars qual_vars]. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [typed_result_qual q_merge_relation qual_prop qual_lvars qual_vars].
    unfold lstore_on_restrict, storeA_on_restrict.
    cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by set_solver.
    setoid_rewrite Hs.
    split; [tauto|]. intros [n [k [z [Hu [Hv [Hw HR]]]]]] .
    split.
    + exists n,k,z. auto.
    + exists (IncorrectMerge.vlist (z)). split; [exact Hw|constructor].
Qed.

Lemma q_merge_relation_store R x y r s :
  qualifier_holds_store (q_merge_relation R (LVFree x) (LVFree y) (LVFree r)) s <->
  exists xs ys zs, s !! x = Some (IncorrectMerge.vlist xs) /\
    s !! y = Some (IncorrectMerge.vlist ys) /\
    s !! r = Some (IncorrectMerge.vlist zs) /\ R xs ys zs.
Proof.
  unfold qualifier_holds_store.
  cbn [q_merge_relation qual_lvars qual_prop].
  split.
  - intros [Hlc [Hscope H]]. unfold lstore_on_lift_store in H.
    cbn [lso_store storeAO_store] in H.
    setoid_rewrite storeA_restrict_lookup in H.
    rewrite !decide_True in H by set_solver.
    setoid_rewrite lstore_lift_free_lookup_free in H. exact H.
  - intros H. assert (Hscope : lvars_fv ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]}) ⊆ dom (s : StoreT)).
    { destruct H as [a [b [c [Hx [Hy [Hr HR]]]]]].
      rewrite !lvars_fv_union,!lvars_fv_singleton_free.
      assert (x ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto).
      assert (y ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto).
      assert (r ∈ (dom (s : gmap atom value) : aset)) by (apply elem_of_dom; eauto). set_solver. }
    assert (Hlc : lc_lvars ({[LVFree x]} ∪ {[LVFree y]} ∪ {[LVFree r]})).
    { intros [j|a] Ha; [set_solver|exact I]. }
    exists Hlc,Hscope. unfold lstore_on_lift_store. cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by set_solver.
    setoid_rewrite lstore_lift_free_lookup_free. exact H.
Qed.
Lemma q_merge_relation_open_store R x y r s :
  r ∉ ({[x;y]} : aset) ->
  qualifier_holds_store (qual_open_atom 0 r (typed_result_qual TList
    (q_merge_relation R (LVFree x) (LVFree y) (LVBound 0)))) s <->
  exists xs ys zs, s !! x = Some (IncorrectMerge.vlist xs) /\
    s !! y = Some (IncorrectMerge.vlist ys) /\
    s !! r = Some (IncorrectMerge.vlist zs) /\ R xs ys zs.
Proof.
  intros Hr. rewrite q_merge_relation_typed,q_merge_relation_open.
  base_swap_normalize. apply q_merge_relation_store.
Qed.
