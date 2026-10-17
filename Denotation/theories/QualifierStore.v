(** Store-locality interfaces for qualifiers, including explicit support. *)
From Denotation Require Import Notation TypeDenote TypeDenoteRegular ConditionalCoverage BaseCoverage ResultQualifier.
From ContextLogic Require Import FormulaAtom.
From ContextBasicDenotation Require Import TermOpen TermEval TermSyntax.

Lemma qualifier_holds_store_scope q (σ : StoreT) :
  qualifier_holds_store q σ -> qual_dom q ⊆ dom (σ : StoreT).
Proof. destruct q as [D P]. intros [_ [H _]]. exact H. Qed.

Lemma qualifier_holds_store_eq_on q (σ τ : StoreT) :
  store_restrict σ (qual_dom q) = store_restrict τ (qual_dom q) ->
  qualifier_holds_store q σ -> qualifier_holds_store q τ.
Proof.
  destruct q as [D P]. cbn [qual_dom qual_lvars]. intros Hsame.
  intros [Hlc [Hscope HP]].
  assert (Hscope' : lvars_fv D ⊆ dom (τ : StoreT)).
  { pose proof (f_equal (fun s : StoreT => dom (s : StoreT)) Hsame) as HD.
    rewrite !store_restrict_dom_set in HD. clear -Hscope HD. set_solver. }
  exists Hlc, Hscope'.
  assert (Hlift : lstore_on_lift_store D σ Hlc Hscope =
      lstore_on_lift_store D τ Hlc Hscope').
  { apply lstore_on_ext. exact (lifted_projection_eq_of_atom_projection σ τ D Hsame). }
  rewrite <- Hlift. exact HP.
Qed.

Lemma qualifier_holds_typed_result_lookup b φ y (σ : StoreT) :
  qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) σ ->
  exists v, σ !! y = Some v.
Proof.
  intros H. apply qualifier_holds_store_scope in H.
  rewrite opened_typed_base_qual_dom in H.
  apply (proj1 (elem_of_dom (σ : gmap atom value) y)). apply H. set_solver.
Qed.

Lemma store_insert_restrict_notin (σ : StoreT) X y v :
  y ∉ X -> store_restrict (<[y:=v]> σ) X = store_restrict σ X.
Proof. intros Hy. exact (storeA_restrict_insert_notin (V:=value) (K:=atom) σ X y v Hy). Qed.

Lemma opened_typed_qualifier_normalize b φ y (σ τ : StoreT) v :
  y ∉ qual_dom φ ->
  store_restrict τ (qual_dom φ) = store_restrict σ (qual_dom φ) ->
  τ !! y = Some v ->
  qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) τ ->
  qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ)) (<[y:=v]> σ).
Proof.
  intros Hy Hsame Hv Hq. eapply qualifier_holds_store_eq_on; [|exact Hq].
  rewrite opened_typed_base_qual_dom. apply store_projection_eq_with_result.
  - rewrite store_insert_restrict_notin by exact Hy. exact Hsame.
  - symmetry. transitivity (Some v); [apply map_lookup_insert|symmetry; exact Hv].
Qed.

Lemma store_restrict_eq_lookup (σ τ : StoreT) X x v :
  x ∈ X -> store_restrict σ X = store_restrict τ X ->
  σ !! x = Some v -> τ !! x = Some v.
Proof.
  intros Hx Hsame Hv.
  pose proof (f_equal (fun s : StoreT => s !! x) Hsame) as Heq.
  exact (eq_trans (eq_sym (store_restrict_lookup_at τ X x Hx))
    (eq_trans (eq_sym Heq) (eq_trans (store_restrict_lookup_at σ X x Hx) Hv))).
Qed.

Lemma store_restrict_eq_on (σ τ : StoreT) X :
  (forall x, x ∈ X -> σ !! x = τ !! x) -> store_restrict σ X = store_restrict τ X.
Proof.
  intros Hlook. apply storeA_map_eq. intros x.
  destruct (decide (x ∈ X)) as [Hx|Hx].
  - exact (eq_trans (store_restrict_lookup_at σ X x Hx)
      (eq_trans (Hlook x Hx) (eq_sym (store_restrict_lookup_at τ X x Hx)))).
  - exact (eq_trans (storeA_restrict_lookup_none_r (V:=value) (K:=atom) σ X x Hx)
      (eq_sym (storeA_restrict_lookup_none_r (V:=value) (K:=atom) τ X x Hx))).
Qed.

Lemma opened_expr_result_qual e y :
  lc_tm e -> y ∉ fv_tm e ->
  qual_open_atom 0 y (expr_result_qual e (LVBound 0)) =
  expr_result_qual e (LVFree y).
Proof.
  intros He Hy.
  pose proof (formula_open_expr_result_atom_formula 0 y e (LVBound 0) Hy) as Hopen.
  unfold expr_result_atom_formula in Hopen.
  rewrite formula_open_atom,(open_rec_lc_tm e He 0 (vfvar y)) in Hopen.
  rewrite swap_l in Hopen.
  exact (f_equal (fun f : FormulaT => match f with
    | FAtom q => q | _ => qual_top end) Hopen).
Qed.

Lemma expr_result_qual_store_elim e y (σ : StoreT) :
  qualifier_holds_store (expr_result_qual e (LVFree y)) σ ->
  exists v, σ !! y = Some v /\ tm_eval_in_store σ e v.
Proof.
  unfold qualifier_holds_store,expr_result_qual.
  cbn [qual_lvars qual_prop].
  intros [Hlc [Hscope [_ [v [Hy Heval]]]]].
  exists v. split.
  - unfold lstore_on_lift_store in Hy. cbn [lso_store storeAO_store] in Hy.
    apply storeA_restrict_lookup_some in Hy as [_ Hy].
    rewrite lstore_lift_free_lookup_free in Hy. exact Hy.
  - unfold lstore_on_lift_store in Heval. cbn [lso_store storeAO_store] in Heval.
    apply (proj1 (expr_eval_in_store_restrict_lvars e (lstore_lift_free σ)
      (tm_lvars e ∪ {[LVFree y]}) v ltac:(set_solver))). exact Heval.
Qed.
