(** Revised paper, Figure 6: integer may/must examples.
    The older natural-number specifications remain in [MayMust]. *)
From CaseStudy Require Import CaseTypes.
From CoreLang Require Import Sugar BasicTypingProps.
From Denotation Require Import ResultQualifier.
From ContextTypeLanguage Require Import WF.
From Stdlib Require Import ZArith Lia.

Definition vint (z : Z) : value := vconst (cint z).
Definition int_pred (P : Z -> Prop) : type_qualifier :=
  param_result_qual TInt ∅ (fun _ v => exists z, v = vint z /\ P z).
Definition OInt (P : Z -> Prop) : context_ty := CTOver TInt (int_pred P).
Definition UInt (P : Z -> Prop) : context_ty := CTUnder TInt (int_pred P).

Definition may_help_must_g_ty : context_ty :=
  CTArrow (OInt (fun _ => True)) (OInt (fun z => z <> 0%Z)).
Definition may_help_must_ty : context_ty :=
  CTArrow (UInt (fun z => z = 0%Z))
    (CTWand (UInt (fun z => (0 <= z <= 10)%Z)) (UInt (fun z => z = 1%Z))).
Definition must_help_may_g_ty : context_ty :=
  CTInter (CTArrow (OInt (fun _ => True)) (OInt (fun z => (0 < z)%Z)))
    (CTArrow (UInt (fun _ => True)) (UInt (fun z => (0 < z)%Z))).
Definition must_help_may_ty : context_ty :=
  CTArrow (UInt (fun _ => True))
    (CTSum (OInt (fun z => z = 2%Z)) (OInt (fun z => z = 5%Z))).

(** User-requested variant of Figure 6(a): y >= 10.
    On integers this is y > 9, using the existing strict comparison primitive. *)
Lemma may_help_must_ge10_test z :
  Z.gtb z 9 = true <-> (10 <= z)%Z.
Proof. rewrite Z.gtb_lt. lia. Qed.
Definition may_help_must (g : atom) : value :=
  vlam TInt (tret (vlam TInt
    (tlete (tprim (op_int_gt 9) (vbvar 0))
      (tmatch (vbvar 0)
        (tlete (tapp (vfvar g) (vbvar 2))
          (tprim op_int_plus1 (vbvar 0)))
        (tprim op_int_plus1 (vbvar 2)))))).

(** λx. let a = g x in if a > 3 then 5 else 2. *)
Definition must_help_may (g : atom) : value :=
  vlam TInt (tlete (tapp (vfvar g) (vbvar 0))
    (tlete (tprim (op_int_gt 3) (vbvar 0))
      (tmatch (vbvar 0) (tret (vint 5)) (tret (vint 2))))).

Lemma int_pred_wf d D P :
  wf_context_ty_at d D (UInt P).
Proof. apply param_result_qual_wf. set_solver. Qed.

Lemma int_pred_over_wf d D P :
  wf_context_ty_at d D (OInt P).
Proof. exact (int_pred_wf d D P). Qed.

Lemma int_pred_dom P : qual_dom (int_pred P) = ∅.
Proof. apply param_result_qual_dom. Qed.

Lemma int_pred_fv (pol : bool) P :
  fv_cty (match pol with true => OInt P | false => UInt P end) = ∅.
Proof.
  destruct pol.
  - pose proof (basic_context_ty_fv_subset ∅ _ (int_pred_over_wf 0 ∅ P)). set_solver.
  - pose proof (basic_context_ty_fv_subset ∅ _ (int_pred_wf 0 ∅ P)). set_solver.
Qed.

Lemma may_help_must_g_wf d D : wf_context_ty_at d D may_help_must_g_ty.
Proof. split; [apply int_pred_over_wf|apply int_pred_over_wf]. Qed.
Lemma may_help_must_wf d D : wf_context_ty_at d D may_help_must_ty.
Proof. split; [apply int_pred_wf|]. split; apply int_pred_wf. Qed.
Lemma must_help_may_g_wf d D : wf_context_ty_at d D must_help_may_g_ty.
Proof.
  split; [split; apply int_pred_over_wf|].
  split; [split; apply int_pred_wf|reflexivity].
Qed.
Lemma must_help_may_wf d D : wf_context_ty_at d D must_help_may_ty.
Proof. split; [apply int_pred_wf|]. split; [apply int_pred_over_wf|
  split; [apply int_pred_over_wf|reflexivity]]. Qed.

Lemma mm_insert_lookup (Δ : gmap atom ty) x y U T :
  x <> y -> Δ !! y = Some T -> (<[x:=U]> Δ) !! y = Some T.
Proof. intros Hxy Hy. exact (eq_trans (map_lookup_insert_ne Δ x y U ltac:(congruence)) Hy). Qed.

Lemma may_help_must_basic (Δ : gmap atom ty) g :
  Δ !! g = Some (TArrow TInt TInt) ->
  value_has_type Δ (may_help_must g) (TArrow TInt (TArrow TInt TInt)).
Proof.
  intros Hg. unfold may_help_must.
  apply VT_Lam with (L:={[g]}). intros x Hx. apply not_elem_of_singleton in Hx.
  change (tm_has_type (<[x:=TBase TInt]> Δ)
    (tret (vlam TInt
      (tlete (tprim (op_int_gt 9) (vbvar 0))
        (tmatch (vbvar 0)
          (tlete (tapp (vfvar g) (vfvar x)) (tprim op_int_plus1 (vbvar 0)))
          (tprim op_int_plus1 (vfvar x)))))) (TArrow TInt TInt)).
  apply TT_Ret, VT_Lam with (L:={[g;x]}). intros y Hy.
  apply not_elem_of_union in Hy as [Hyg Hyx].
  apply not_elem_of_singleton in Hyg, Hyx.
  change (tm_has_type (<[y:=TBase TInt]>(<[x:=TBase TInt]>Δ))
    (tlete (tprim (op_int_gt 9) (vfvar y))
      (tmatch (vbvar 0)
        (tlete (tapp (vfvar g) (vfvar x)) (tprim op_int_plus1 (vbvar 0)))
        (tprim op_int_plus1 (vfvar x)))) (TBase TInt)).
  apply TT_Let with (T1:=TBase TBool) (L:={[g;x;y]}).
  - eapply TT_Op; [reflexivity|]. apply VT_FVar, map_lookup_insert.
  - intros b Hb.
    apply not_elem_of_union in Hb as [Hbgx Hby].
    apply not_elem_of_union in Hbgx as [Hbg Hbx].
    apply not_elem_of_singleton in Hbg,Hbx,Hby.
    change (tm_has_type
      (<[b:=TBase TBool]>(<[y:=TBase TInt]>(<[x:=TBase TInt]>Δ)))
      (tmatch (vfvar b)
        (tlete (tapp (vfvar g) (vfvar x)) (tprim op_int_plus1 (vbvar 0)))
        (tprim op_int_plus1 (vfvar x))) (TBase TInt)).
    apply TT_Match.
    + apply VT_FVar, map_lookup_insert.
    + apply TT_Let with (T1:=TBase TInt) (L:=∅).
      * eapply TT_App with (s1:=TBase TInt); apply VT_FVar.
        -- eapply mm_insert_lookup; [congruence|].
           eapply mm_insert_lookup; [congruence|].
           eapply mm_insert_lookup; [congruence|exact Hg].
        -- eapply mm_insert_lookup; [congruence|].
           eapply mm_insert_lookup; [congruence|]. apply map_lookup_insert.
      * intros a _. change (tm_has_type
          (<[a:=TBase TInt]>(<[b:=TBase TBool]>(<[y:=TBase TInt]>(<[x:=TBase TInt]>Δ))))
          (tprim op_int_plus1 (vfvar a)) (TBase TInt)).
        eapply TT_Op; [reflexivity|]. apply VT_FVar, map_lookup_insert.
    + eapply TT_Op; [reflexivity|]. apply VT_FVar.
      eapply mm_insert_lookup; [congruence|].
           eapply mm_insert_lookup; [congruence|]. apply map_lookup_insert.
Qed.

Lemma must_help_may_basic (Δ : gmap atom ty) g :
  Δ !! g = Some (TArrow TInt TInt) ->
  value_has_type Δ (must_help_may g) (TArrow TInt TInt).
Proof.
  intros Hg. unfold must_help_may.
  apply VT_Lam with (L:={[g]}). intros x Hx. apply not_elem_of_singleton in Hx.
  change (tm_has_type (<[x:=TBase TInt]>Δ)
    (tlete (tapp (vfvar g) (vfvar x))
      (tlete (tprim (op_int_gt 3) (vbvar 0))
        (tmatch (vbvar 0) (tret (vint 5)) (tret (vint 2))))) (TBase TInt)).
  apply TT_Let with (T1:=TBase TInt) (L:=∅).
  - eapply TT_App with (s1:=TBase TInt); apply VT_FVar.
    + eapply mm_insert_lookup; [congruence|exact Hg].
    + apply map_lookup_insert.
  - intros a _. change (tm_has_type (<[a:=TBase TInt]>(<[x:=TBase TInt]>Δ))
      (tlete (tprim (op_int_gt 3) (vfvar a))
        (tmatch (vbvar 0) (tret (vint 5)) (tret (vint 2)))) (TBase TInt)).
    apply TT_Let with (T1:=TBase TBool) (L:=∅).
    + eapply TT_Op; [reflexivity|]. apply VT_FVar, map_lookup_insert.
    + intros b _. change (tm_has_type
        (<[b:=TBase TBool]>(<[a:=TBase TInt]>(<[x:=TBase TInt]>Δ)))
        (tmatch (vfvar b) (tret (vint 5)) (tret (vint 2))) (TBase TInt)).
      apply TT_Match; [apply VT_FVar, map_lookup_insert|
        apply TT_Ret, VT_Const|apply TT_Ret, VT_Const].
Qed.
