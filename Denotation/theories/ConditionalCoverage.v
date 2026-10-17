(** Base-variable denotations yield conditional coverage in their original
    world, rather than unrelated witnesses from separate projections. *)
From Denotation Require Import Notation TypeDenote TypePersistBase.
From ContextLogic Require Import FormulaUnderCoverage.
From ContextBasicDenotation Require Import TreeCoverage.

Lemma base_result_parameters (φ : type_qualifier) z :
  z ∉ qual_dom φ ->
  lvars_fv (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]}) = qual_dom φ.
Proof.
  intros Hz. rewrite qual_open_atom_vars, lvars_fv_difference_singleton_free,
    lvars_fv_open.
  unfold qual_dom in *. destruct (decide (0%nat ∈ lvars_bv (qual_vars φ)));
    set_solver.
Qed.

Lemma opened_typed_base_qual_dom b (φ : type_qualifier) z :
  qual_dom (qual_open_atom 0 z (typed_result_qual b φ)) = qual_dom φ ∪ {[z]}.
Proof.
  unfold qual_dom at 1. rewrite qual_open_atom_vars.
  cbn [typed_result_qual qual_vars qual_lvars].
  rewrite lvars_open_union, set_swap_singleton, swap_l,
    lvars_fv_union, lvars_fv_singleton_free, lvars_fv_open.
  unfold qual_dom, qual_vars.
  destruct (decide (0%nat ∈ lvars_bv (qual_lvars φ))).
  all: apply set_eq; intros x;
    rewrite !elem_of_union, !elem_of_difference, !elem_of_singleton,
      ?elem_of_empty; tauto.
Qed.

Lemma opened_typed_base_qual_lc b (φ : type_qualifier) z :
  lc_context_ty (CTUnder b φ) -> z ∉ qual_dom φ ->
  lc_lvars (qual_vars (qual_open_atom 0 z (typed_result_qual b φ))).
Proof.
  intros Hlc Hz. cbn [lc_context_ty cty_lc_at] in Hlc.
  rewrite qual_open_atom_vars. cbn [typed_result_qual qual_vars qual_lvars].
  intros [[|j]|x] Hu; [| |exact I].
  - change (LVBound 0 ∈ set_swap (LVBound 0) (LVFree z)
      (qual_vars φ ∪ {[LVBound 0]})) in Hu.
    rewrite set_swap_elem, swap_l in Hu.
    apply Hz. unfold qual_dom. apply lvars_fv_elem. set_solver.
  - change (LVBound (S j) ∈ set_swap (LVBound 0) (LVFree z)
      (qual_vars φ ∪ {[LVBound 0]})) in Hu.
    rewrite set_swap_elem, swap_fresh in Hu by discriminate.
    assert (Hj : S j ∈ lvars_bv (qual_vars φ)) by
      (apply lvars_bv_elem; set_solver).
    specialize (Hlc _ Hj). lia.
Qed.

Lemma over_ret_var_store_holds gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ -> z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar z)) ->
  forall σ, (m : WorldT) σ ->
    qualifier_holds_store (qual_open_atom 0 z (typed_result_qual b φ)) σ.
Proof.
  intros HΣ Hz Hden.
  apply fib_over_atom_store_holds with
    (D := qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]}).
  exact (ty_denote_gas_over_ret_fvar_self_body gas Σ b φ z m HΣ Hz Hden).
Qed.

Lemma under_ret_var_covers_value gas Σ b φ z (m : WfWorldT) σ v :
  lty_env_closed Σ -> z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) (tret (vfvar z)) ->
  (m : WorldT) σ ->
  qualifier_holds_store (qual_open_atom 0 z (typed_result_qual b φ)) (<[z:=v]> σ) ->
  exists σ', (m : WorldT) σ' /\
    store_restrict σ' (qual_dom φ) = store_restrict σ (qual_dom φ) /\
    σ' !! z = Some v.
Proof.
  intros HΣ Hz Hden Hσ Hv.
  pose proof (ty_denote_gas_under_ret_fvar_self_body gas Σ b φ z m HΣ Hz Hden)
    as Hbody.
  unfold under_open_body in Hbody.
  destruct (fib_under_atom_covers_store m
    (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]})
    (qual_open_atom 0 z (typed_result_qual b φ)) σ (<[z:=v]> σ)
    Hbody Hσ ltac:(rewrite (base_result_parameters φ z Hz);
      apply storeA_restrict_insert_notin; exact Hz) Hv)
    as [σ' [Hσ' [Hparams Hresult]]].
  exists σ'. split; [exact Hσ'|]. split.
  - rewrite (base_result_parameters φ z Hz) in Hparams. exact Hparams.
  - rewrite <- lstore_lift_free_lookup_free.
    eapply storeA_restrict_lookup_transport;
      [|symmetry; exact Hresult|rewrite lstore_lift_free_lookup_free;
        apply lookup_insert_eq].
    rewrite qual_open_atom_vars.
    unfold typed_result_qual. cbn [qual_vars qual_lvars].
    rewrite lvars_open_union.
    apply elem_of_union_r.
    change (LVFree z ∈ set_swap (LVBound 0) (LVFree z) {[LVBound 0]}).
    rewrite set_swap_singleton, swap_l. set_solver.
Qed.

Lemma under_ret_var_conditional_coverage gas Σ b φ z (m : WfWorldT)
    (P : StoreT -> value -> Prop) :
  lty_env_closed Σ -> z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) (tret (vfvar z)) ->
  (forall σ v, (m : WorldT) σ -> P (store_restrict σ (qual_dom φ)) v ->
    qualifier_holds_store (qual_open_atom 0 z (typed_result_qual b φ)) (<[z:=v]> σ)) ->
  variable_covers_on m (qual_dom φ) z P.
Proof.
  intros HΣ Hz Hden HP σ v Hσ Hv.
  exact (under_ret_var_covers_value gas Σ b φ z m σ v
    HΣ Hz Hden Hσ (HP σ v Hσ Hv)).
Qed.
