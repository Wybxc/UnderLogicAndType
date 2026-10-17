(** Under support changes are justified here only when all parameters are
    fixed throughout the current world.  No arbitrary support extension
    or stability under removing stores is assumed. *)
From Denotation Require Import Notation TypeDenote TypeDenoteRegular
  BaseCoverage QualifierStore ResultQualifier.

Lemma under_denote_fixed_parameters gas1 gas2 Σ b φ1 φ2 e (m : WfWorldT) F σfix :
  lty_env_closed Σ -> lc_tm e ->
  lc_context_ty (CTUnder b φ1) -> lc_context_ty (CTUnder b φ2) ->
  qual_dom φ1 ⊆ F -> qual_dom φ2 ⊆ F ->
  (forall σ, (m : WorldT) σ -> store_restrict σ F = σfix) ->
  (forall y τ, y ∉ F -> store_restrict τ F = σfix ->
    (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ1)) τ <->
     qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ2)) τ)) ->
  m ⊨ ty_denote_gas (S gas1) Σ (CTUnder b φ1) e ->
  m ⊨ ty_denote_gas 0 Σ (CTUnder b φ2) e ->
  m ⊨ ty_denote_gas gas2 Σ (CTUnder b φ2) e.
Proof.
  intros HΣ Hlce Hlc1 Hlc2 HF1 HF2 Hfixed Hequiv Hsource Hzero.
  assert (Hsource_fresh : forall y, y ∉ world_dom (m : WorldT) ∪ F ->
      y ∉ world_dom (m : WorldT) ∪ qual_dom φ1) by
    (intros y Hy; clear -Hy HF1; set_solver).
  apply (under_denote_intro_store_coverage gas2 Σ b φ2 e m
    (world_dom (m : WorldT) ∪ F)); [exact Hlc2|exact Hzero| |].
  - intros y Hy σ Hσ.
    destruct (under_denote_elim_store_coverage gas1 Σ b φ1 e m y
      HΣ Hlce Hlc1 Hsource (Hsource_fresh y Hy)) as [Hne _].
    destruct (Hne σ Hσ) as [τ [Hq Hsame]].
    destruct (qualifier_holds_typed_result_lookup b φ1 y τ Hq) as [v Hv].
    assert (HyF : y ∉ F) by (clear -Hy; set_solver).
    assert (Hy1 : y ∉ qual_dom φ1) by (clear -HyF HF1; set_solver).
    assert (Hy2 : y ∉ qual_dom φ2) by (clear -HyF HF2; set_solver).
    assert (Hnorm : qualifier_holds_store
      (qual_open_atom 0 y (typed_result_qual b φ1)) (<[y:=v]> σ)).
    { eapply opened_typed_qualifier_normalize; eassumption. }
    assert (HnormF : store_restrict (<[y:=v]> σ) F = σfix).
    { rewrite store_insert_restrict_notin by exact HyF. apply Hfixed. exact Hσ. }
    exists (<[y:=v]> σ). split.
    + apply (proj1 (Hequiv y _ HyF HnormF)). exact Hnorm.
    + apply store_insert_restrict_notin. exact Hy2.
  - intros y Hy σ τ Hσ Hsame Hq.
    destruct (under_denote_elim_store_coverage gas1 Σ b φ1 e m y
      HΣ Hlce Hlc1 Hsource (Hsource_fresh y Hy)) as [_ Hcover].
    destruct (qualifier_holds_typed_result_lookup b φ2 y τ Hq) as [v Hv].
    assert (HyF : y ∉ F) by (clear -Hy; set_solver).
    assert (Hy1 : y ∉ qual_dom φ1) by (clear -HyF HF1; set_solver).
    assert (Hy2 : y ∉ qual_dom φ2) by (clear -HyF HF2; set_solver).
    assert (Hnorm2 : qualifier_holds_store
      (qual_open_atom 0 y (typed_result_qual b φ2)) (<[y:=v]> σ)).
    { eapply opened_typed_qualifier_normalize; eassumption. }
    assert (HnormF : store_restrict (<[y:=v]> σ) F = σfix).
    { rewrite store_insert_restrict_notin by exact HyF. apply Hfixed. exact Hσ. }
    assert (Hnorm1 : qualifier_holds_store
      (qual_open_atom 0 y (typed_result_qual b φ1)) (<[y:=v]> σ)).
    { apply (proj2 (Hequiv y _ HyF HnormF)). exact Hnorm2. }
    destruct (Hcover σ (<[y:=v]> σ) Hσ
      (store_insert_restrict_notin σ _ y v Hy1) Hnorm1)
      as [σ' [v' [Hσ' [_ [Hyv' Heval]]]]].
    assert (Hyv : (<[y:=v]> σ : StoreT) !! y = Some v) by apply map_lookup_insert.
    assert (Some v' = Some v) as Hvv by exact (eq_trans (eq_sym Hyv') Hyv).
    inversion Hvv; subst v'.
    exists σ', v. split; [exact Hσ'|]. split.
    + exact (storeA_restrict_eq_mono (V:=value) (K:=atom) σ' σ (qual_dom φ2) F HF2
        (eq_trans (Hfixed σ' Hσ') (eq_sym (Hfixed σ Hσ)))).
    + split; assumption.
Qed.
