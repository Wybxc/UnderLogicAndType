(** Conditional under coverage in the original world.  Fixed parameters
    are substituted only inside their fiber; witnesses retain those
    parameters and are lifted back to the same source world. *)
From ContextLogic Require Import FormulaAtom FormulaSemantics FormulaUnderAtom FormulaConnectives.

Section UnderCoverage.
Context {V : Type} `{ValueSig V}.
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ) (at level 70).

Lemma lstore_lift_fixed_substitution σfix σ D :
  store_restrict σ (dom (σfix : StoreT)) = σfix ->
  storeA_restrict (atom_store_to_lvar_store σfix) D =
    storeA_restrict (lstore_lift_free σ)
      (D ∩ dom (atom_store_to_lvar_store σfix : gmap logic_var V)).
Proof.
  intros Hfix. set (ρ := atom_store_to_lvar_store σfix).
  change (storeA_restrict ρ D = storeA_restrict (lstore_lift_free σ)
    (D ∩ dom (ρ : gmap logic_var V))).
  apply storeA_map_eq. intros [j|x].
  - rewrite !storeA_restrict_lookup.
    subst ρ. rewrite atom_store_to_lvar_store_lookup_bound_none,
      lstore_lift_free_lookup_bound. repeat case_decide; reflexivity.
  - rewrite !storeA_restrict_lookup.
    subst ρ. rewrite atom_store_to_lvar_store_lookup_free,
      lstore_lift_free_lookup_free, atom_store_to_lvar_store_dom.
    destruct (decide (LVFree x ∈ D)) as [HxD|HxD].
    + destruct (decide (x ∈ dom (σfix : StoreT))) as [Hx|Hx].
      * assert (Hxl : (σ : gmap atom V) !! x = (σfix : gmap atom V) !! x).
        { pose proof (f_equal (fun st : StoreT => st !! x) Hfix) as Hlook.
          change ((storeA_restrict σ (dom (σfix : StoreT)) : StoreT) !! x =
            σfix !! x) in Hlook.
          rewrite (storeA_restrict_lookup (V:=V) (K:=atom)
            σ (dom (σfix : StoreT)) x) in Hlook.
          destruct (decide (x ∈ dom (σfix : StoreT)));
            [exact Hlook|contradiction]. }
        case_decide.
        -- symmetry. exact Hxl.
        -- exfalso. unfold lvars_of_atoms in *. set_solver.
      * assert (Hnone : (σfix : gmap atom V) !! x = None) by
          (apply not_elem_of_dom_1; exact Hx).
        case_decide.
        -- exfalso. unfold lvars_of_atoms in *. set_solver.
        -- exact Hnone.
    + case_decide; [exfalso; set_solver|reflexivity].
Qed.

Lemma qualifier_msubst_store_holds_of_restrict σfix σ q :
  store_restrict σ (dom (σfix : StoreT)) = σfix ->
  qualifier_holds_store q σ ->
  qualifier_holds_store (qual_msubst_store σfix q) σ.
Proof.
  destruct q as [D P]. intros Hfix [Hlc [HD HP]].
  set (ρ := atom_store_to_lvar_store σfix).
  assert (HlcR : lc_lvars (D ∖ dom (ρ : gmap logic_var V))).
  { intros u Hu. apply Hlc. set_solver. }
  assert (HR : lvars_fv (D ∖ dom (ρ : gmap logic_var V)) ⊆ dom (σ : StoreT)).
  { intros x Hx. apply HD. apply lvars_fv_elem in Hx.
    apply lvars_fv_elem. set_solver. }
  change (exists HlcR HR,
    P (lstore_on_mlsubst_back D ρ
      (lstore_on_lift_store (D ∖ dom (ρ : gmap logic_var V)) σ HlcR HR))).
  exists HlcR, HR.
  rewrite (lstore_on_mlsubst_back_lift_store D ρ σ Hlc HD HlcR HR);
    [exact HP|].
  apply lstore_lift_fixed_substitution. exact Hfix.
Qed.

Lemma qualifier_msubst_store_holds_to_restrict σfix σ q :
  store_restrict σ (dom (σfix : StoreT)) = σfix ->
  qual_dom q ⊆ dom (σ : StoreT) ->
  qualifier_holds_store (qual_msubst_store σfix q) σ ->
  qualifier_holds_store q σ.
Proof.
  destruct q as [D P]. intros Hfix HD Hsubst.
  set (ρ := atom_store_to_lvar_store σfix) in *.
  change (exists HlcR HR,
    P (lstore_on_mlsubst_back D ρ
      (lstore_on_lift_store (D ∖ dom (ρ : gmap logic_var V)) σ HlcR HR))) in Hsubst.
  destruct Hsubst as [HlcR [HR HP]].
  assert (Hlc : lc_lvars D).
  { intros [j|x] Hu; [|exact I].
    apply (HlcR (LVBound j)). apply elem_of_difference. split; [exact Hu|].
    subst ρ. rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms. set_solver. }
  exists Hlc, HD.
  rewrite <- (lstore_on_mlsubst_back_lift_store D ρ σ Hlc HD HlcR HR);
    [exact HP|apply lstore_lift_fixed_substitution; exact Hfix].
Qed.

Lemma fib_over_atom_store_holds (m : WfWorldT) D q :
  m ⊨ FFibVars D (FOver (FAtom q)) ->
  forall σ, (m : WorldT) σ -> qualifier_holds_store q σ.
Proof.
  intros Hover σ Hσ.
  apply res_models_FFibVars_iff in Hover as [Hscope [HlcD Hfib]].
  destruct (res_fiber_from_projection_of_store_any_domain m (lvars_fv D) σ Hσ)
    as [mfib [Hproj Hσfib]].
  specialize (Hfib _ _ Hproj).
  change (mfib ⊨ FOver (FAtom (qual_msubst_store
    (store_restrict σ (lvars_fv D)) q))) in Hfib.
  pose proof (res_models_over_FAtom_store_holds mfib _ Hfib σ Hσfib) as Hholds.
  eapply qualifier_msubst_store_holds_to_restrict; [| |exact Hholds].
  - exact (res_fiber_from_projection_store_restrict m mfib (lvars_fv D)
      (store_restrict σ (lvars_fv D)) σ Hproj Hσfib).
  - unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom in Hscope.
    change (qual_dom q ⊆ dom (σ : gmap atom V)).
    rewrite (wfworld_store_dom m σ Hσ). clear -Hscope. set_solver.
Qed.

Lemma qualifier_msubst_store_realize D P σfix
    (s : LStoreOn (D ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V))) :
  lc_lvars D -> dom (σfix : gmap atom V) ⊆ lvars_fv D ->
  P (lstore_on_mlsubst_back D (atom_store_to_lvar_store σfix) s) ->
  exists τ, qualifier_holds_store (tqual D P) τ /\
    store_restrict τ (dom (σfix : gmap atom V)) = σfix /\
    storeA_restrict (lstore_lift_free τ)
      (D ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V)) = lso_store s.
Proof.
  intros Hlc HfixD HP.
  set (ρ := atom_store_to_lvar_store σfix).
  set (sfull := lstore_on_mlsubst_back D ρ s).
  set (τ := atom_store_extend_lstore_on (lvars_fv D) D sfull).
  assert (HτD : dom (τ : gmap atom V) = lvars_fv D).
  { apply atom_store_extend_lstore_on_dom; [exact Hlc|reflexivity]. }
  assert (Hlift : storeA_restrict (lstore_lift_free τ) D = lso_store sfull).
  { apply atom_store_extend_lstore_on_lift_restrict; [exact Hlc|reflexivity]. }
  exists τ. split.
  - assert (HDτ : lvars_fv D ⊆ dom (τ : StoreT)).
    { change (lvars_fv D ⊆ dom (τ : gmap atom V)). rewrite HτD. reflexivity. }
    exists Hlc, HDτ.
    assert (Heq : lstore_on_lift_store D τ Hlc HDτ = sfull).
    { apply lstore_on_ext. exact Hlift. }
    rewrite Heq. exact HP.
  - split.
    + apply storeA_map_eq. intros x. rewrite storeA_restrict_lookup.
      destruct (decide (x ∈ dom (σfix : gmap atom V))) as [Hx|Hx].
      * pose proof (f_equal (fun st : gmap logic_var V => st !! LVFree x) Hlift)
          as Hlook.
        change ((storeA_restrict (lstore_lift_free τ) D : gmap logic_var V)
          !! LVFree x = (lso_store sfull : gmap logic_var V) !! LVFree x) in Hlook.
        pose proof (eq_trans (eq_sym
          (storeA_restrict_lookup (V:=V) (K:=logic_var)
            (lstore_lift_free τ) D (LVFree x))) Hlook) as Hdirect.
        assert (HxD : LVFree x ∈ D) by (apply lvars_fv_elem; apply HfixD; exact Hx).
        destruct (decide (LVFree x ∈ D)); [|contradiction].
        rewrite lstore_lift_free_lookup_free in Hdirect.
        unfold sfull, lstore_on_mlsubst_back in Hdirect.
        cbn [lso_store storeAO_store] in Hdirect.
        rewrite lookup_union_r in Hdirect.
        -- pose proof (eq_trans Hdirect
             (storeA_restrict_lookup (V:=V) (K:=logic_var) ρ D (LVFree x))) as Hout.
           destruct (decide (LVFree x ∈ D)); [|contradiction].
           subst ρ. rewrite atom_store_to_lvar_store_lookup_free in Hout.
           exact Hout.
        -- apply not_elem_of_dom_1. rewrite lso_dom.
           subst ρ. rewrite atom_store_to_lvar_store_dom.
           unfold lvars_of_atoms. set_solver.
      * symmetry. apply not_elem_of_dom_1. exact Hx.
    + rewrite <- (storeA_restrict_twice_subset (lstore_lift_free τ) D
        (D ∖ dom (ρ : gmap logic_var V))) by set_solver.
      rewrite Hlift. unfold sfull, lstore_on_mlsubst_back.
      cbn [lso_store storeAO_store].
      apply storeA_map_eq. intros u. rewrite storeA_restrict_lookup.
      destruct (decide (u ∈ D ∖ dom (ρ : gmap logic_var V))) as [Hu|Hu].
      * rewrite lookup_union_l.
        -- reflexivity.
        -- apply storeA_restrict_lookup_none_l.
           apply not_elem_of_dom_1. clear -Hu. set_solver.
      * symmetry. apply not_elem_of_dom_1. rewrite lso_dom. exact Hu.
Qed.

Lemma fib_under_atom_covers_store (m : WfWorldT) D q σ τ :
  m ⊨ FFibVars D (FUnder (FAtom q)) ->
  (m : WorldT) σ ->
  store_restrict τ (lvars_fv D) = store_restrict σ (lvars_fv D) ->
  qualifier_holds_store q τ ->
  exists σ', (m : WorldT) σ' /\
    store_restrict σ' (lvars_fv D) = store_restrict σ (lvars_fv D) /\
    storeA_restrict (lstore_lift_free σ') (qual_vars q) =
      storeA_restrict (lstore_lift_free τ) (qual_vars q).
Proof.
  intros Hunder Hσ HτD Hτq.
  apply res_models_FFibVars_iff in Hunder as [_ [HlcD Hfib]].
  set (σfix := store_restrict σ (lvars_fv D)).
  destruct (res_fiber_from_projection_of_store_any_domain m (lvars_fv D) σ Hσ)
    as [mfib [Hproj Hσfib]].
  assert (Hfixdom : dom (σfix : gmap atom V) ⊆ lvars_fv D).
  { apply storeA_restrict_dom_subset. }
  assert (Hτfix : store_restrict τ (dom (σfix : gmap atom V)) = σfix).
  { transitivity (store_restrict σ (dom (σfix : gmap atom V))).
    - eapply storeA_restrict_eq_mono; [exact Hfixdom|exact HτD].
    - exact (res_fiber_from_projection_store_restrict m mfib (lvars_fv D)
        σfix σ Hproj Hσfib). }
  specialize (Hfib σfix mfib Hproj).
  change (mfib ⊨ FUnder (FAtom (qual_msubst_store σfix q))) in Hfib.
  pose proof (qualifier_msubst_store_holds_of_restrict σfix τ q Hτfix Hτq)
    as Hτsubst.
  destruct (under_atom_covers_store mfib (qual_msubst_store σfix q) τ Hfib Hτsubst)
    as [σ' [Hσ' Hres]].
  assert (Hσ'fix : store_restrict σ' (dom (σfix : gmap atom V)) = σfix).
  { exact (res_fiber_from_projection_store_restrict m mfib (lvars_fv D)
      σfix σ' Hproj Hσ'). }
  exists σ'. split.
  - eapply res_fiber_from_projection_store_source; eauto.
  - split.
    + exact (res_fiber_from_projection_store_restrict_input m mfib
        (lvars_fv D) σfix σ' Hproj Hσ').
    + assert (Hvars : qual_vars (qual_msubst_store σfix q) =
          qual_vars q ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V)).
      { destruct q; reflexivity. }
      rewrite Hvars in Hres.
      apply storeA_map_eq. intros u.
      rewrite !storeA_restrict_lookup.
      destruct (decide (u ∈ qual_vars q)) as [Hu|Hu]; [|reflexivity].
      destruct (decide (u ∈ dom (atom_store_to_lvar_store σfix : gmap logic_var V)))
        as [Hufix|Hufix].
      * rewrite atom_store_to_lvar_store_dom in Hufix.
        unfold lvars_of_atoms in Hufix.
        apply elem_of_map in Hufix as [x [-> Hx]].
        rewrite !lstore_lift_free_lookup_free.
        pose proof (f_equal (fun st : gmap atom V => st !! x) Hσ'fix) as H1.
        pose proof (f_equal (fun st : gmap atom V => st !! x) Hτfix) as H2.
        rewrite (storeA_restrict_lookup σ' (dom (σfix : gmap atom V)) x) in H1.
        rewrite (storeA_restrict_lookup τ (dom (σfix : gmap atom V)) x) in H2.
        destruct (decide (x ∈ dom (σfix : gmap atom V)));
          [|contradiction].
        exact (eq_trans H1 (eq_sym H2)).
      * pose proof (f_equal (fun st : gmap logic_var V => st !! u) Hres) as Hlook.
        rewrite (storeA_restrict_lookup (V:=V) (K:=logic_var)
          (lstore_lift_free σ')
          (qual_vars q ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V)) u),
          (storeA_restrict_lookup (V:=V) (K:=logic_var)
          (lstore_lift_free τ)
          (qual_vars q ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V)) u)
          in Hlook.
        destruct (decide (u ∈ qual_vars q ∖
            dom (atom_store_to_lvar_store σfix : gmap logic_var V)))
          as [Hin|Hnot]; [exact Hlook|set_solver].
Qed.

Lemma fib_under_atom_inhabited_store (m : WfWorldT) D q σ :
  lc_lvars (qual_vars q) -> D ⊆ qual_vars q ->
  m ⊨ FFibVars D (FUnder (FAtom q)) -> (m : WorldT) σ ->
  exists τ, qualifier_holds_store q τ /\
    store_restrict τ (lvars_fv D) = store_restrict σ (lvars_fv D).
Proof.
  destruct q as [E P]. intros HlcE HDE Hbody Hσ.
  apply res_models_FFibVars_iff in Hbody as [Hscope [HlcD Hfib]].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  { unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars in Hscope. clear -Hscope. set_solver. }
  destruct (res_fiber_from_projection_of_store m (lvars_fv D) σ HDm Hσ)
    as [mfib [Hproj Hσfib]].
  set (σfix := store_restrict σ (lvars_fv D)).
  assert (Hdomfix : dom (σfix : gmap atom V) = lvars_fv D).
  { unfold σfix. rewrite storeA_restrict_dom, (wfworld_store_dom m σ Hσ).
    clear -HDm. set_solver. }
  assert (HfixE : dom (σfix : gmap atom V) ⊆ lvars_fv E).
  { rewrite Hdomfix. apply lvars_fv_mono. exact HDE. }
  pose proof (Hfib σfix mfib Hproj) as Hunder.
  destruct (res_models_under_atom_inhabited mfib _ Hunder)
    as [σres [HlcR [HR HP]]].
  change (P (lstore_on_mlsubst_back E (atom_store_to_lvar_store σfix)
    (lstore_on_lift_store
      (E ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V))
      σres HlcR HR))) in HP.
  destruct (qualifier_msubst_store_realize E P σfix _ HlcE HfixE HP)
    as [τ [Hτ [Hτfix _]]].
  exists τ. split; [exact Hτ|]. rewrite <- Hdomfix. exact Hτfix.
Qed.

Lemma fib_under_atom_intro_store_coverage (m : WfWorldT) D q :
  lc_lvars D -> lc_lvars (qual_vars q) -> D ⊆ qual_vars q ->
  formula_scoped_in_world m (FFibVars D (FUnder (FAtom q))) ->
  (forall σ, (m : WorldT) σ -> exists τ,
    qualifier_holds_store q τ /\
    store_restrict τ (lvars_fv D) = store_restrict σ (lvars_fv D)) ->
  (forall σ τ, (m : WorldT) σ ->
    store_restrict τ (lvars_fv D) = store_restrict σ (lvars_fv D) ->
    qualifier_holds_store q τ ->
    exists σ', (m : WorldT) σ' /\
      store_restrict σ' (lvars_fv D) = store_restrict σ (lvars_fv D) /\
      storeA_restrict (lstore_lift_free σ') (qual_vars q) =
        storeA_restrict (lstore_lift_free τ) (qual_vars q)) ->
  m ⊨ FFibVars D (FUnder (FAtom q)).
Proof.
  destruct q as [E P]. intros HlcD HlcE HDE Hscope Hne Hcover.
  eapply res_models_FFibVars_intro; [exact Hscope|exact HlcD|].
  intros σfix mfib Hproj.
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  { unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars in Hscope. clear -Hscope. set_solver. }
  assert (HEm : lvars_fv E ⊆ world_dom (m : WorldT)).
  { unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom in Hscope.
    intros x Hx. apply Hscope. cbn [qual_vars qual_lvars]. set_solver. }
  assert (Hdomfix : dom (σfix : gmap atom V) = lvars_fv D).
  { pose proof (wfworld_store_dom (res_restrict m (lvars_fv D)) σfix (proj1 Hproj))
      as Hdom. rewrite res_restrict_dom in Hdom. clear -HDm Hdom. set_solver. }
  assert (HfixE : dom (σfix : gmap atom V) ⊆ lvars_fv E).
  { rewrite Hdomfix. apply lvars_fv_mono. exact HDE. }
  destruct (world_wf mfib) as [[σ0 Hσ0] _].
  pose proof (res_fiber_from_projection_store_source m mfib (lvars_fv D)
    σfix σ0 Hproj Hσ0) as Hσ0m.
  pose proof (res_fiber_from_projection_store_restrict_input m mfib (lvars_fv D)
    σfix σ0 Hproj Hσ0) as Hσ0fix.
  change (mfib ⊨ FUnder (FAtom (tqual
    (E ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V))
    (fun s => P (lstore_on_mlsubst_back E (atom_store_to_lvar_store σfix) s))))).
  apply under_atom_intro_store_coverage.
  - intros u Hu. apply HlcE. set_solver.
  - rewrite (res_fiber_from_projection_world_dom m mfib (lvars_fv D) σfix Hproj).
    intros x Hx. apply HEm. apply lvars_fv_elem in Hx.
    apply lvars_fv_elem. set_solver.
  - destruct (Hne σ0 Hσ0m) as [τ [Hτq HτD]].
    assert (Hτfix : store_restrict τ (dom (σfix : gmap atom V)) = σfix).
    { rewrite Hdomfix, HτD. exact Hσ0fix. }
    pose proof (qualifier_msubst_store_holds_of_restrict σfix τ (tqual E P)
      Hτfix Hτq) as Hτsubst.
    destruct Hτsubst as [HlcR [HR HP]].
    eexists. exact HP.
  - intros s Hs.
    destruct (qualifier_msubst_store_realize E P σfix s HlcE HfixE Hs)
      as [τ [Hτq [Hτfix Hτres]]].
    assert (HτD : store_restrict τ (lvars_fv D) = store_restrict σ0 (lvars_fv D)).
    { rewrite <- Hdomfix, Hτfix. symmetry. rewrite Hdomfix. exact Hσ0fix. }
    destruct (Hcover σ0 τ Hσ0m HτD Hτq) as [σ' [Hσ'm [Hσ'D Hσ'q]]].
    exists σ'. split.
    + destruct Hproj as [_ Hfiber].
      change ((mfib : WorldT) = raw_fiber (m : WorldT) σfix) in Hfiber.
      rewrite Hfiber. split; [exact Hσ'm|].
      change (store_restrict σ' (dom (σfix : gmap atom V)) = σfix).
      rewrite Hdomfix, Hσ'D. exact Hσ0fix.
    + transitivity (storeA_restrict (lstore_lift_free τ)
        (E ∖ dom (atom_store_to_lvar_store σfix : gmap logic_var V)));
        [|exact Hτres].
      eapply storeA_restrict_eq_mono with (Y := E); [set_solver|exact Hσ'q].
Qed.

End UnderCoverage.
