(** Explicitly supported intermediate types for the positive-size BST step.
    The right qualifier retains the left-tree parameter even though its
    mathematical predicate does not inspect that parameter. *)
From CaseStudy Require Import CaseTypes BSTGenerator BSTSpecFacts.
From Denotation Require Import Notation ResultQualifier TreeCoverage.
From ContextTyping Require Import Typing.

Definition bst_pivot_qual (S : aset) (n : nat) : type_qualifier :=
  param_result_qual TNat S (fun _ v =>
    exists p, v = vconst (cnat p) /\ 1 <= p <= n).

Definition bst_root_qual (S : aset) xp (a : nat) : type_qualifier :=
  param_result_qual TNat (S ∪ {[xp]}) (fun s v =>
    exists p k, s !! xp = Some (vconst (cnat p)) /\
      v = vconst (cnat k) /\ k = a + p).

Definition bst_left_qual (S : aset) xp (n a : nat) : type_qualifier :=
  param_result_qual TTree (S ∪ {[xp]}) (fun s v =>
    exists p l, s !! xp = Some (vconst (cnat p)) /\
      v = vconst (ctree l) /\ 1 <= p <= n /\ bst_spec (p - 1) a l).

Definition bst_right_qual (S : aset) xp xl (n a : nat) : type_qualifier :=
  param_result_qual TTree (S ∪ {[xp;xl]}) (fun s v =>
    exists p rr, s !! xp = Some (vconst (cnat p)) /\
      v = vconst (ctree rr) /\ 1 <= p <= n /\ bst_spec (n - p) (a + p) rr).

Definition bst_result_qual (S : aset) (n a : nat) : type_qualifier :=
  param_result_qual TTree S (fun _ v =>
    exists t, v = vconst (ctree t) /\ bst_spec n a t).

Lemma bst_node_under_graph_spec n a S xp xk xl xr :
  0 < n ->
  xp ∉ S -> xk ∉ S ∪ {[xp]} -> xl ∉ S ∪ {[xp]} -> xr ∉ S ∪ {[xp;xl]} ->
  node_under_graph_spec S xp xk xl xr
    (bst_pivot_qual S n) (bst_root_qual S xp a)
    (bst_left_qual S xp n a) (bst_right_qual S xp xl n a)
    (bst_result_qual S n a)
    (fun _ p => 1 <= p <= n)
    (fun _ p k => k = a + p)
    (fun _ p l => 1 <= p <= n /\ bst_spec (p - 1) a l)
    (fun _ p _ rr => 1 <= p <= n /\ bst_spec (n - p) (a + p) rr)
    (fun _ t => bst_spec n a t).
Proof.
  intros Hn Hxp Hxk Hxl Hxr. constructor.
  - exact Hxp.
  - exact Hxk.
  - exact Hxl.
  - exact Hxr.
  - apply param_result_qual_dom.
  - apply param_result_qual_dom.
  - apply param_result_qual_dom.
  - apply param_result_qual_dom.
  - apply param_result_qual_dom.
  - intros σ p HS Hp. unfold bst_pivot_qual.
    apply typed_param_result_qual_open_store; [exact Hxp|].
    split.
    + change (S ⊆ dom (<[xp:=vconst (cnat p)]> σ : gmap atom value)).
      rewrite store_insert_dom. clear -HS. set_solver.
    + exists (vconst (cnat p)). split; [apply (fin_maps.lookup_insert_eq (M:=gmap atom))|].
      split; [apply BVT_Const|]. exists p. auto.
  - intros σ p l HS Hpl [Hp Hl]. unfold bst_left_qual.
    apply typed_param_result_qual_open_store; [exact Hxl|].
    split.
    + change (S ∪ {[xp]} ⊆ dom (<[xl:=vconst (ctree l)]> σ : gmap atom value)).
      assert (Hpd : xp ∈ dom (σ : gmap atom value)) by (eapply elem_of_dom_2; exact Hpl).
      rewrite store_insert_dom. clear -HS Hpd. set_solver.
    + exists (vconst (ctree l)). split; [apply (fin_maps.lookup_insert_eq (M:=gmap atom))|].
      split; [apply BVT_Const|]. exists p, l. split.
      * rewrite store_restrict_lookup_at by set_solver.
        rewrite store_insert_lookup_ne by (clear -Hxl; set_solver). exact Hpl.
      * auto.
  - intros σ p l rr HS Hpl Hll [Hp Hr]. unfold bst_right_qual.
    apply typed_param_result_qual_open_store; [exact Hxr|].
    split.
    + change (S ∪ {[xp;xl]} ⊆ dom (<[xr:=vconst (ctree rr)]> σ : gmap atom value)).
      assert (Hpd : xp ∈ dom (σ : gmap atom value)) by (eapply elem_of_dom_2; exact Hpl).
      assert (Hld : xl ∈ dom (σ : gmap atom value)) by (eapply elem_of_dom_2; exact Hll).
      rewrite store_insert_dom. clear -HS Hpd Hld. set_solver.
    + exists (vconst (ctree rr)). split; [apply (fin_maps.lookup_insert_eq (M:=gmap atom))|].
      split; [apply BVT_Const|]. exists p, rr. split.
      * rewrite store_restrict_lookup_at by set_solver.
        rewrite store_insert_lookup_ne by (clear -Hxr; set_solver). exact Hpl.
      * auto.
  - intros σ p HS Hpl Hq. unfold bst_root_qual in Hq.
    apply typed_param_result_qual_open_store in Hq; [|exact Hxk].
    destruct Hq as [_ [v [Hkv [_ [p' [k [Hp' [-> Hk]]]]]]]].
    rewrite store_restrict_lookup_at in Hp' by set_solver.
    rewrite Hpl in Hp'. inversion Hp'; subst p'. exists k. auto.
  - intros s t Ht.
    destruct (bst_spec_positive_decompose n a t Hn Ht) as [p [l [rr [Hp [-> [Hl Hr]]]]]].
    exists p, (a + p), l, rr.
    split; [reflexivity|]. split; [exact Hp|].
    split; [split; assumption|]. split; [split; assumption|].
    intros k' Hk'. exact Hk'.
  - intros y τ Hy Hq. unfold bst_result_qual in Hq.
    apply typed_param_result_qual_open_store in Hq; [|exact Hy].
    destruct Hq as [_ [v [Hvy [_ [t [-> Ht]]]]]]. exists t. auto.
  - intros y s Hy Hs.
    destruct (bst_spec_inhabited n a) as [t Ht].
    exists (<[y:=vconst (ctree t)]> s). split.
    + unfold bst_result_qual. apply typed_param_result_qual_open_store; [exact Hy|].
      split.
      * change (S ⊆ dom (<[y:=vconst (ctree t)]> s : gmap atom value)).
        rewrite store_insert_dom.
        rewrite Hs. set_solver.
      * exists (vconst (ctree t)). split; [apply (fin_maps.lookup_insert_eq (M:=gmap atom))|].
        split; [apply BVT_Const|]. exists t. auto.
    + etransitivity; [exact (storeA_restrict_insert_notin (V:=value) (K:=atom)
        s S y (vconst (ctree t)) Hy)|].
      apply storeA_restrict_idemp_eq. exact Hs.
Qed.

(** A genuine node typing derivation once the four variable derivations
    have been obtained in the restored, unclassified continuation. *)
Lemma bst_node_context_typed Φ Σ Γ n a S xp xk xl xr :
  0 < n ->
  xp ∉ S -> xk ∉ S ∪ {[xp]} -> xl ∉ S ∪ {[xp]} -> xr ∉ S ∪ {[xp;xl]} ->
  context_typing_wf Σ Γ (tnode (vfvar xk) (vfvar xl) (vfvar xr))
    (CTUnder TTree (bst_result_qual S n a)) ->
  has_context_type Φ Σ Γ (tret (vfvar xp)) (CTUnder TNat (bst_pivot_qual S n)) ->
  has_context_type Φ Σ Γ (tret (vfvar xk)) (CTOver TNat (bst_root_qual S xp a)) ->
  has_context_type Φ Σ Γ (tret (vfvar xl)) (CTUnder TTree (bst_left_qual S xp n a)) ->
  has_context_type Φ Σ Γ (tret (vfvar xr)) (CTUnder TTree (bst_right_qual S xp xl n a)) ->
  has_context_type Φ Σ Γ (tnode (vfvar xk) (vfvar xl) (vfvar xr))
    (CTUnder TTree (bst_result_qual S n a)).
Proof.
  intros Hn Hxp Hxk Hxl Hxr Hwf HP HK HL HR.
  eapply CT_NodeUnderGraph with (S:=S) (xp:=xp)
    (φP:=bst_pivot_qual S n) (φK:=bst_root_qual S xp a)
    (φL:=bst_left_qual S xp n a) (φR:=bst_right_qual S xp xl n a);
    [exact Hwf|exact (bst_node_under_graph_spec n a S xp xk xl xr Hn Hxp Hxk Hxl Hxr)|
     exact HP|exact HK|exact HL|exact HR].
Qed.
