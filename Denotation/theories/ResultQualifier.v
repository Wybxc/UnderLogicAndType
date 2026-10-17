(** Result predicates with explicit parameter support.  The support is part
    of the qualifier, including parameters unused by its predicate. *)
From Denotation Require Import Notation TypeDenote.
From ContextLogic Require Import FormulaAtom.

Definition param_result_qual (b : base_ty) (X : aset)
    (P : StoreT -> value -> Prop) : type_qualifier :=
  tqual (lvars_of_atoms X ∪ {[LVBound 0]}) (fun s =>
    exists v, (lso_store s : LStoreT) !! LVBound 0 = Some v /\
      basic_value_has_ltype ∅ v (TBase b) /\ P (lstore_free_part (lso_store s)) v).

Lemma param_result_qual_dom b X P : qual_dom (param_result_qual b X P) = X.
Proof.
  unfold qual_dom, param_result_qual. cbn [qual_lvars].
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound. set_solver.
Qed.

Lemma param_result_qual_lc b X P : lc_context_ty (CTUnder b (param_result_qual b X P)).
Proof.
  cbn [lc_context_ty cty_lc_at param_result_qual qual_vars qual_lvars].
  intros j Hj. apply lvars_bv_elem in Hj.
  apply elem_of_union in Hj as [Hj|Hj].
  - unfold lvars_of_atoms in Hj. apply elem_of_map in Hj as [x [Hbad _]]. discriminate.
  - apply elem_of_singleton in Hj. inversion Hj. lia.
Qed.

Lemma param_result_qual_open_vars b X P y :
  y ∉ X ->
  qual_vars (qual_open_atom 0 y (param_result_qual b X P)) =
    lvars_of_atoms X ∪ {[LVFree y]}.
Proof.
  intros Hy. rewrite qual_open_atom_vars.
  cbn [param_result_qual qual_vars qual_lvars]. rewrite lvars_open_union.
  rewrite set_swap_singleton, swap_l.
  f_equal. apply set_eq. intros [j|x]; rewrite set_swap_elem.
  - destruct j as [|j].
    + rewrite swap_l. unfold lvars_of_atoms. rewrite !elem_of_map.
      split; intros [a [Hbad Ha]]; inversion Hbad; subst; contradiction.
    + rewrite swap_fresh by discriminate.
      reflexivity.
  - destruct (decide (x = y)) as [->|Hxy].
    + rewrite swap_r. unfold lvars_of_atoms. rewrite !elem_of_map.
      split; intros [a [Hbad Ha]]; inversion Hbad; subst; contradiction.
    + rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma param_result_qual_open_store b X P y σ :
  y ∉ X ->
  qualifier_holds_store (qual_open_atom 0 y (param_result_qual b X P)) σ <->
  X ⊆ dom (σ : StoreT) /\ exists v, σ !! y = Some v /\
    basic_value_has_ltype ∅ v (TBase b) /\ P (store_restrict σ X) v.
Proof.
  intros Hy.
  set (D := lvars_of_atoms X ∪ {[LVBound 0]}).
  assert (HDopen : lvars_open 0 y D = lvars_of_atoms X ∪ {[LVFree y]}).
  { exact (param_result_qual_open_vars b X P y Hy). }
  assert (Hlc : lc_lvars (lvars_open 0 y D)).
  { rewrite HDopen. intros [j|x] H; [|exact I].
    apply elem_of_union in H as [H|H]; [|set_solver].
    unfold lvars_of_atoms in H. apply elem_of_map in H as [a [Hbad _]]. discriminate. }
  assert (Hfv : lvars_fv (lvars_open 0 y D) = X ∪ {[y]}).
  { rewrite HDopen, lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free. reflexivity. }
  assert (Hback : forall Hscope : lvars_fv (lvars_open 0 y D) ⊆ dom (σ : StoreT),
    let s := lstore_on_open_back 0 y D
      (lstore_on_lift_store (lvars_open 0 y D) σ Hlc Hscope) in
    (lso_store s : LStoreT) !! LVBound 0 = σ !! y /\
    lstore_free_part (lso_store s) = store_restrict σ X).
  { intros Hscope. cbn zeta. split.
    - change ((storeA_swap (LVBound 0) (LVFree y)
        (storeA_restrict (lstore_lift_free σ) (lvars_open 0 y D)) : LStoreT) !!
        LVBound 0 = σ !! y).
      etransitivity; [exact (storeA_swap_lookup_inv (V:=value) (K:=logic_var)
        (LVBound 0) (LVFree y)
        (storeA_restrict (lstore_lift_free σ) (lvars_open 0 y D)) (LVBound 0))|].
      rewrite swap_l, storeA_restrict_lookup.
      rewrite HDopen. destruct (decide (LVFree y ∈ lvars_of_atoms X ∪ {[LVFree y]}));
        [apply lstore_lift_free_lookup_free|set_solver].
    - apply storeA_map_eq. intros x. unfold lstore_free_part.
      rewrite lstore_to_store_lookup.
      change ((storeA_swap (LVBound 0) (LVFree y)
        (storeA_restrict (lstore_lift_free σ) (lvars_open 0 y D)) : LStoreT) !!
        LVFree x = (storeA_restrict σ X : StoreT) !! x).
      etransitivity; [exact (storeA_swap_lookup_inv (V:=value) (K:=logic_var)
        (LVBound 0) (LVFree y)
        (storeA_restrict (lstore_lift_free σ) (lvars_open 0 y D)) (LVFree x))|].
      etransitivity; [exact (storeA_restrict_lookup (V:=value) (K:=logic_var)
        (lstore_lift_free σ) (lvars_open 0 y D)
        (swap (LVBound 0) (LVFree y) (LVFree x)))|].
      symmetry. etransitivity; [exact (storeA_restrict_lookup (V:=value) (K:=atom)
        σ X x)|].
      rewrite HDopen.
      destruct (decide (x ∈ X)) as [Hx|Hx].
      + rewrite swap_fresh by (try discriminate; congruence).
        destruct (decide (LVFree x ∈ lvars_of_atoms X ∪ {[LVFree y]})).
        * symmetry. apply lstore_lift_free_lookup_free.
        * exfalso. apply n. apply elem_of_union_l.
          unfold lvars_of_atoms. apply elem_of_map. exists x. auto.
      + destruct (decide (x = y)) as [->|Hxy].
        * rewrite swap_r.
          destruct (decide (LVBound 0 ∈ lvars_of_atoms X ∪ {[LVFree y]}));
            [exfalso; unfold lvars_of_atoms in *; set_solver|reflexivity].
        * rewrite swap_fresh by congruence.
          destruct (decide (LVFree x ∈ lvars_of_atoms X ∪ {[LVFree y]}));
            [exfalso; unfold lvars_of_atoms in *; set_solver|reflexivity]. }

  unfold qualifier_holds_store, qual_open_atom, param_result_qual.
  fold D. split.
  - intros [Hlc' [Hscope [v [Hv [Htyped HP]]]]].
    assert (Hlc' = Hlc) as -> by apply proof_irrelevance.
    destruct (Hback Hscope) as [Hval Hparams].
    rewrite Hval in Hv. rewrite Hparams in HP.
    split; [pose proof Hscope as Hsc; rewrite Hfv in Hsc; clear -Hsc; set_solver|].
    exists v. auto.
  - intros [HX [v [Hyv [Htyped HP]]]].
    assert (Hscope : lvars_fv (lvars_open 0 y D) ⊆ dom (σ : StoreT)).
    { rewrite Hfv. assert (y ∈ dom (σ : StoreT)).
      { change (y ∈ dom (σ : gmap atom value)). eapply elem_of_dom_2. exact Hyv. }
      clear -HX H. set_solver. }
    exists Hlc, Hscope.
    destruct (Hback Hscope) as [Hval Hparams].
    exists v. rewrite Hval, Hparams. auto.
Qed.

Lemma typed_param_result_qual b X P :
  typed_result_qual b (param_result_qual b X P) = param_result_qual b X P.
Proof.
  apply qual_ext.
  - cbn [typed_result_qual param_result_qual qual_vars qual_lvars]. set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [typed_result_qual param_result_qual qual_prop qual_vars qual_lvars
      lstore_on_restrict storeA_on_restrict lso_store storeAO_store].
    assert (Hr : storeA_restrict s1 (lvars_of_atoms X ∪ {[LVBound 0]}) = s2).
    { rewrite Hs. apply storeA_restrict_idemp_eq. exact Hdom2. }
    rewrite Hr, Hs. split.
    + intros [H _]. exact H.
    + intros [v [Hv [Htyped HP]]]. split; [exists v; auto|exists v; auto].
Qed.

Lemma typed_param_result_qual_open_store b X P y σ :
  y ∉ X ->
  qualifier_holds_store
    (qual_open_atom 0 y (typed_result_qual b (param_result_qual b X P))) σ <->
  X ⊆ dom (σ : StoreT) /\ exists v, σ !! y = Some v /\
    basic_value_has_ltype ∅ v (TBase b) /\ P (store_restrict σ X) v.
Proof. intros Hy. rewrite typed_param_result_qual. apply param_result_qual_open_store. exact Hy. Qed.

Lemma store_restrict_lookup_at (σ : StoreT) X x :
  x ∈ X -> (store_restrict σ X : StoreT) !! x = σ !! x.
Proof.
  intros Hx. etransitivity;
    [exact (storeA_restrict_lookup (V:=value) (K:=atom) σ X x)|].
  destruct (decide (x ∈ X)); [reflexivity|contradiction].
Qed.

Lemma store_insert_dom (σ : StoreT) x v :
  dom (<[x:=v]> σ : StoreT) = {[x]} ∪ dom (σ : StoreT).
Proof. exact (fin_map_dom.dom_insert_L (M:=gmap atom) (D:=gset atom) σ x v). Qed.

Lemma store_insert_lookup_ne (σ : StoreT) x y v :
  x <> y -> (<[x:=v]> σ : StoreT) !! y = σ !! y.
Proof. intros Hxy. exact (fin_maps.lookup_insert_ne (M:=gmap atom) σ x y v Hxy). Qed.

Lemma store_restrict_dom_set (σ : StoreT) X :
  dom (store_restrict σ X : StoreT) = dom (σ : StoreT) ∩ X.
Proof. exact (storeA_restrict_dom (V:=value) (K:=atom) σ X). Qed.

Lemma param_result_qual_wf d D b X P :
  X ⊆ D -> wf_context_ty_at d D (CTUnder b (param_result_qual b X P)).
Proof.
  intros HX. cbn [wf_context_ty_at param_result_qual qual_vars qual_lvars].
  unfold lvars_wf_at. intros [k|x] H.
  - cbn [lvar_wf_at]. apply elem_of_union in H as [H|H].
    + unfold lvars_of_atoms in H. apply elem_of_map in H as [z [Hbad _]]. discriminate.
    + apply elem_of_singleton in H. inversion H. lia.
  - cbn [lvar_wf_at]. apply elem_of_union in H as [H|H].
    + unfold lvars_of_atoms in H. apply elem_of_map in H as [z [Hz Hzin]].
      inversion Hz; subst z. apply HX. exact Hzin.
    + apply elem_of_singleton in H. discriminate.
Qed.
