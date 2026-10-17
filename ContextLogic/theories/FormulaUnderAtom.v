(** Store-level characterization of under atoms.  Nonemptiness is explicit:
    coverage of an empty predicate alone does not satisfy [FUnder]. *)
From ContextLogic Require Import FormulaSemantics FormulaConnectives FormulaAtom FormulaNotation.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.

Section UnderAtom.
Context {V : Type} `{ValueSig V}.
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ) (at level 70).

Lemma res_models_under_atom_inhabited (m : WfWorldT) q :
  m ⊨ FUnder (FAtom q) -> exists σ, qualifier_holds_store q σ.
Proof.
  unfold res_models. cbn [formula_measure res_models_fuel].
  intros [_ [mo [_ Hq]]].
  destruct (world_wf mo) as [[σ Hσ] _].
  exists σ. eapply res_models_FAtom_store_holds; eauto.
Qed.

Corollary under_false_atom_impossible (m : WfWorldT) D :
  ~ m ⊨ FUnder (FAtom (tqual D (fun _ => False))).
Proof.
  intros Hunder.
  destruct (res_models_under_atom_inhabited m _ Hunder)
    as [σ [Hlc [Hscope Hfalse]]]. exact Hfalse.
Qed.

Lemma under_atom_store_coverage (m : WfWorldT) D P :
  m ⊨ FUnder (FAtom (tqual D P)) ->
  forall s : LStoreOn D, P s ->
    exists σ, (m : WorldT) σ /\
      storeA_restrict (lstore_lift_free σ) D = lso_store s.
Proof.
  unfold res_models. cbn [formula_measure res_models_fuel].
  intros [_ [mo [[Hdom Hsub] [_ [Hlc [HD Hiff]]]]]] s Hs.
  pose proof (proj1 (Hiff s) Hs) as Hmem.
  unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
  cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
  destruct Hmem as [ρ [[σD [[σ [Hσ HσD]] Hρ]] HρD]].
  exists σ. split; [apply Hsub; exact Hσ|].
  rewrite Hρ, <- HσD in HρD.
  rewrite lstore_lift_free_restrict_fv_lvars_eq in HρD. exact HρD.
Qed.

Lemma under_atom_covers_store (m : WfWorldT) q τ :
  m ⊨ FUnder (FAtom q) -> qualifier_holds_store q τ ->
  exists σ, (m : WorldT) σ /\
    storeA_restrict (lstore_lift_free σ) (qual_vars q) =
    storeA_restrict (lstore_lift_free τ) (qual_vars q).
Proof.
  destruct q as [D P]. intros Hunder [Hlc [HD HP]].
  exact (under_atom_store_coverage m D P Hunder
    (lstore_on_lift_store D τ Hlc HD) HP).
Qed.

Lemma under_atom_intro_store_coverage (m : WfWorldT) D P :
  lc_lvars D -> lvars_fv D ⊆ world_dom (m : WorldT) ->
  (exists s : LStoreOn D, P s) ->
  (forall s : LStoreOn D, P s ->
    exists σ, (m : WorldT) σ /\
      storeA_restrict (lstore_lift_free σ) D = lso_store s) ->
  m ⊨ FUnder (FAtom (tqual D P)).
Proof.
  intros Hlc HD Hne Hcover.
  assert (Hholds : forall s : LStoreOn D, P s ->
      exists σ, (m : WorldT) σ /\ qualifier_holds_store (tqual D P) σ /\
        storeA_restrict (lstore_lift_free σ) D = lso_store s).
  { intros s Hs. destruct (Hcover s Hs) as [σ [Hσ Hproj]].
    assert (HDσ : lvars_fv D ⊆ dom (σ : StoreT)).
    { change (lvars_fv D ⊆ dom (σ : gmap atom V)).
      rewrite (wfworld_store_dom m σ Hσ). exact HD. }
    exists σ. split; [exact Hσ|]. split; [|exact Hproj].
    exists Hlc, HDσ.
    assert (Heq : lstore_on_lift_store D σ Hlc HDσ = s).
    { apply lstore_on_ext. exact Hproj. }
    rewrite Heq. exact Hs. }
  destruct Hne as [s0 Hs0].
  destruct (Hholds s0 Hs0) as [σ0 [Hσ0 [HP0 _]]].
  set (w := ({| worldA_dom := world_dom (m : WorldT);
    worldA_stores := fun σ => (m : WorldT) σ /\ qualifier_holds_store (tqual D P) σ |} : WorldT)).
  assert (Hwwf : wf_world w).
  { split.
    - exists σ0. split; assumption.
    - intros σ [Hσ _]. exact (wfworld_store_dom m σ Hσ). }
  set (mo := (exist _ w Hwwf : WfWorldT)).
  assert (HDmo : lvars_fv D ⊆ world_dom (mo : WorldT)) by exact HD.
  assert (Hatom : mo ⊨ FAtom (tqual D P)).
  { unfold res_models. cbn [formula_measure res_models_fuel].
    split.
    - unfold formula_scoped_in_world. rewrite formula_fv_atom. exact HDmo.
    - exists Hlc, HDmo. intros s. split.
      + intros Hs. destruct (Hholds s Hs) as [σ [Hσ [HP Hproj]]].
        assert (HDσ : lvars_fv D ⊆ dom (σ : StoreT)).
        { change (lvars_fv D ⊆ dom (σ : gmap atom V)).
          rewrite (wfworld_store_dom m σ Hσ). exact HD. }
        assert (Heq : lstore_on_lift_store D σ Hlc HDσ = s).
        { apply lstore_on_ext. exact Hproj. }
        rewrite <- Heq. apply lstore_in_lworld_on_lift_store_of_world.
        split; assumption.
      + intros Hmem.
        unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
        cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
        destruct Hmem as [ρ [[σD [[σ [[Hσ HP] HσD]] Hρ]] HρD]].
        destruct HP as [Hlcσ [HDσ HP]].
        assert (Heq : lstore_on_lift_store D σ Hlcσ HDσ = s).
        { apply lstore_on_ext. rewrite Hρ, <- HσD in HρD.
          rewrite lstore_lift_free_restrict_fv_lvars_eq in HρD. exact HρD. }
        rewrite <- Heq. exact HP. }
  unfold res_models. cbn [formula_measure res_models_fuel].
  split.
  - unfold formula_scoped_in_world. rewrite formula_fv_under, formula_fv_atom. exact HD.
  - exists mo. split; [|exact Hatom].
    split; [reflexivity|]. intros σ [Hσ _]. exact Hσ.
Qed.

End UnderAtom.
