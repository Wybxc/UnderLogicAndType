From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* Set-of-results checks only: no claim about has_context_type or termination. *)
Definition f_a (g : Z -> Z) (x y : Z) : Z :=
  if Z.gtb y 10 then g x + 1 else x + 1.

Lemma a_product_witness (X Y : Z -> Prop) (g : Z -> Z) :
  X 0 -> (forall y, 0 <= y <= 10 -> Y y) ->
  exists x y, X x /\ Y y /\ f_a g x y = 1.
Proof.
  intros HX HY. exists 0, 0. split; [exact HX|].
  split; [apply HY; lia|reflexivity].
Qed.

Definition correlated (x y : Z) : Prop :=
  (x = 0 /\ y = 11) \/ (x = 1 /\ 0 <= y <= 10).

Lemma correlated_covers_x_zero : exists y, correlated 0 y.
Proof. exists 11. left. auto. Qed.

Lemma correlated_covers_y :
  forall y, 0 <= y <= 10 -> exists x, correlated x y.
Proof. intros y Hy. exists 1. right. auto. Qed.

Lemma correlated_never_one :
  forall x y, correlated x y -> f_a (fun _ => 1) x y <> 1.
Proof.
  intros x y [[-> ->]|[-> Hy]]; unfold f_a.
  - discriminate.
  - assert (H : Z.gtb y 10 = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite H. discriminate.
Qed.

Definition branch_b (a : Z) : Z := if Z.gtb a 3 then 5 else 2.

Lemma b_positive_coverage_is_enough (A : Z -> Prop) :
  (forall a, 0 < a -> A a) ->
  forall v, (exists a, A a /\ v = branch_b a) <-> v = 2 \/ v = 5.
Proof.
  intros Hcover v. split.
  - intros [a [_ ->]]. unfold branch_b.
    destruct (Z.gtb a 3); auto.
  - intros [Hv | Hv]; subst v.
    + exists 1. split; [apply Hcover; lia|reflexivity].
    + exists 4. split; [apply Hcover; lia|reflexivity].
Qed.

Lemma b_safe_constant_two_not_tight :
  (forall a, a = 1 -> 0 < a) /\
  ~ (exists a, a = 1 /\ branch_b a = 5).
Proof. split; [intros; lia|]. intros [a [-> H]]. discriminate. Qed.

Lemma b_safe_constant_five_not_tight :
  (forall a, a = 4 -> 0 < a) /\
  ~ (exists a, a = 4 /\ branch_b a = 2).
Proof. split; [intros; lia|]. intros [a [-> H]]. discriminate. Qed.

(* C includes the entire closure state; E includes arbitrary extra variables.
   Equality of the C/Y projection to a product is the essential hypothesis.
   No type denotation is assumed stable under arbitrary subset selection. *)
Lemma product_filter_preserves_closure_projection
    (C E : Type) (W : C -> Z -> E -> Prop)
    (closures : C -> Prop) (inputs B : Z -> Prop) :
  (forall c y, (exists e, W c y e) <-> closures c /\ inputs y) ->
  (exists y, inputs y /\ B y) ->
  forall c, (exists y e, W c y e /\ B y) <-> closures c.
Proof.
  intros Hproject [y0 [Hy0 HB0]] c. split.
  - intros [y [e [HW _]]].
    pose proof (proj1 (Hproject c y) (ex_intro _ e HW)) as Hpair.
    exact (proj1 Hpair).
  - intros Hc.
    destruct (proj2 (Hproject c y0) (conj Hc Hy0)) as [e He].
    exists y0, e. auto.
Qed.

Print Assumptions a_product_witness.
Print Assumptions correlated_never_one.
Print Assumptions b_positive_coverage_is_enough.
Print Assumptions product_filter_preserves_closure_projection.
