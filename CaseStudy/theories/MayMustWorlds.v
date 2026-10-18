(** Capability partitions used by revised Figure 6.
    These are resource lemmas, not additional typing rules. *)
From CoreLang Require Import Syntax.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceInterface ResourceAlgebra.
From Stdlib Require Import Logic.Classical_Prop.

Local Notation StoreT := (gmap atom value).
Local Notation WorldT := (World (V := value)).
Local Notation WfWorldT := (WfWorld (V := value)).

Definition select_world (m : WfWorldT) (P : StoreT -> Prop)
    (Hne : exists s, (m : WorldT) s /\ P s) : WfWorldT.
Proof.
  refine (exist _ {| worldA_dom := world_dom (m : WorldT);
    worldA_stores := fun s => (m : WorldT) s /\ P s |} _).
  split; [exact Hne|].
  intros s [Hs _]. exact (wfworld_store_dom m s Hs).
Defined.

Lemma select_world_dom m P Hne :
  world_dom (select_world m P Hne : WorldT) = world_dom (m : WorldT).
Proof. reflexivity. Qed.

Lemma select_world_subset m P Hne :
  res_subset (select_world m P Hne) m.
Proof. split; [reflexivity|intros s Hs; exact (proj1 Hs)]. Qed.

Lemma select_world_restrict (m n : WfWorldT) (P : StoreT -> Prop) Hm Hn :
  m ⊑ n ->
  (forall s, P s <-> P (store_restrict s (world_dom (m : WorldT)))) ->
  select_world m P Hm ⊑ select_world n P Hn.
Proof.
  intros Hle HP.
  change (raw_le (m : WorldT) (n : WorldT)) in Hle.
  pose proof (raw_le_dom (m : WorldT) (n : WorldT) Hle) as Hdom.
  change (raw_le (select_world m P Hm) (select_world n P Hn)).
  unfold raw_le, rawA_le in Hle |- *.
  apply world_ext.
  - cbn [select_world rawA_restrict world_dom].
    cbn [world_dom] in *. set_solver.
  - intros s. cbn [select_world rawA_restrict]. split.
    + intros [Hs Hps]. rewrite Hle in Hs.
      destruct Hs as [t [Ht Hts]].
      exists t. split; [split; [exact Ht|]|exact Hts].
      apply (proj2 (HP t)).
      change (P (storeA_restrict t (worldA_dom (m : WorldT)))).
      rewrite Hts. exact Hps.
    + intros [t [[Ht HPt] Hts]]. split.
      * rewrite Hle. exists t. auto.
      * change (store_restrict t (world_dom (m : WorldT)) = s) in Hts.
        rewrite <- Hts. exact (proj1 (HP t) HPt).
Qed.

Lemma select_world_partition m P HP HnotP :
  exists Hdef : raw_sum_defined
      (select_world m P HP) (select_world m (fun s => ~ P s) HnotP),
    res_sum (select_world m P HP)
      (select_world m (fun s => ~ P s) HnotP) Hdef = m.
Proof.
  exists eq_refl. apply wfworld_eq_by_dom_stores; [reflexivity|].
  intros s. change (((m : WorldT) s /\ P s) \/ ((m : WorldT) s /\ ~ P s) <-> (m : WorldT) s).
  destruct (classic (P s)); tauto.
Qed.

Lemma select_world_product_compat (c d : WfWorldT) P Hd :
  world_compat c d -> world_compat c (select_world d P Hd).
Proof. intros Hc s t Hs [Ht _]. exact (Hc s t Hs Ht). Qed.

(** Filtering a product by a condition on its right component preserves the
    entire left component, including closures and correlated captured data. *)
Lemma select_world_product (c d : WfWorldT) P Hd Hcd Hprod :
  (forall s t, (c : WorldT) s -> (d : WorldT) t ->
    P (s ∪ t) <-> P t) ->
  select_world (res_product c d Hcd) P Hprod =
  res_product c (select_world d P Hd)
    (select_world_product_compat c d P Hd Hcd).
Proof.
  intros HP. apply wfworld_eq_by_dom_stores; [reflexivity|].
  intros s. change
    (((exists a b, (c : WorldT) a /\ (d : WorldT) b /\
        storeA_compat a b /\ s = a ∪ b) /\ P s) <->
      (exists a b, (c : WorldT) a /\ ((d : WorldT) b /\ P b) /\
        storeA_compat a b /\ s = a ∪ b)).
  split.
  - intros [[a [b [Ha [Hb [Hab ->]]]]] Hs].
    exists a,b. repeat split; try assumption.
    exact (proj1 (HP a b Ha Hb) Hs).
  - intros [a [b [Ha [[Hb HPb] [Hab ->]]]]]. split.
    + exists a,b. auto.
    + exact (proj2 (HP a b Ha Hb) HPb).
Qed.

Lemma select_world_product_left (c d : WfWorldT) P
    (Hd : exists s, (d : WorldT) s /\ P s) Hcd Hprod :
  (forall s t, (c : WorldT) s -> (d : WorldT) t ->
    P (s ∪ t) <-> P t) ->
  c ⊑ select_world (res_product c d Hcd) P Hprod.
Proof.
  intros HP. rewrite (select_world_product c d P Hd Hcd Hprod HP).
  apply res_product_le_l.
Qed.

Lemma select_world_extension_keeps_left (c d n : WfWorldT) P Hcd
    (Hd : exists s, (d : WorldT) s /\ P s)
    (Hprod : exists s, (res_product c d Hcd : WorldT) s /\ P s) Hn :
  res_product c d Hcd ⊑ n ->
  (forall s, P s <-> P (store_restrict s
    (world_dom (res_product c d Hcd : WorldT)))) ->
  (forall s t, (c : WorldT) s -> (d : WorldT) t ->
    P (s ∪ t) <-> P t) ->
  c ⊑ select_world n P Hn.
Proof.
  intros Hle Hlocal HP.
  etransitivity.
  - exact (select_world_product_left c d P Hd Hcd Hprod HP).
  - exact (select_world_restrict _ _ _ Hprod Hn Hle Hlocal).
Qed.
