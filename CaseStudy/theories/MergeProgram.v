(** Revised Figure 8: the erroneous merge, using the existing subtraction library. *)
From CaseStudy Require Export DisproveMerge NatArithmetic NatArithmeticStages.
From Stdlib Require Import List Lia.
Import ListNotations.

Module IncorrectMerge.
Definition self : atom := 101%positive.
Definition l1 : atom := 102%positive.
Definition l2 : atom := 103%positive.
Definition h1 : atom := 104%positive.
Definition t1 : atom := 105%positive.
Definition h2 : atom := 106%positive.
Definition t2 : atom := 107%positive.
Definition tail : atom := 108%positive.
Definition diff : atom := 109%positive.
Definition flag : atom := 110%positive.
Definition tmp : atom := 111%positive.

Definition cons2 a b t :=
  NatArithmetic.let_in tmp (tcons b t) (tcons a (vfvar tmp)).
Definition branch hd tl body :=
  close_tm tl 1 (close_tm hd 0 body).
Definition named_body : tm :=
  tmatchlist (vfvar l2) (tret (vfvar l1))
    (branch h2 t2
      (tmatchlist (vfvar l1) (tret (vfvar l2))
        (branch h1 t1
          (NatArithmetic.let_in tail
            (NatArithmetic.app2 (vfvar self) (vfvar t1) (vfvar t2))
            (NatArithmetic.let_in diff
              (NatArithmetic.app2 NatArithmetic.sub_value (vfvar h2) (vfvar h1))
              (NatArithmetic.let_in flag (tprim op_eq0 (vfvar diff))
                (tmatch (vfvar flag)
                  (NatArithmetic.let_in diff
                    (NatArithmetic.app2 NatArithmetic.sub_value (vfvar h1) (vfvar h2))
                    (NatArithmetic.let_in flag (tprim op_eq0 (vfvar diff))
                      (tmatch (vfvar flag)
                        (tcons (vfvar h1) (vfvar tail))
                        (cons2 (vfvar h2) (vfvar h1) (vfvar tail)))))
                  (cons2 (vfvar h1) (vfvar h2) (vfvar tail))))))))).
Definition merge_value :=
  NatArithmetic.fix_fun self l1 TList (TArrow TList TList)
    (tret (NatArithmetic.lam l2 TList named_body)).
Definition vlist xs := vconst (clist xs).
Definition call xs ys := NatArithmetic.app2 merge_value (vlist xs) (vlist ys).
Definition partial vx : value :=
  match merge_value with
  | vfix _ (vlam _ (tret v)) => open_value 0 merge_value (open_value 1 vx v)
  | _ => vconst cunit
  end.
Definition body vx vy :=
  match partial vx with vlam _ e => open_tm 0 vy e | _ => tret (vconst cunit) end.
Fixpoint result (xs ys : list nat) : list nat :=
  match xs,ys with
  | _,[] => xs
  | [],_ => ys
  | a::xs',b::ys' =>
    let t := result xs' ys' in
    match Nat.eqb (b-a) 0 with
    | true => match Nat.eqb (a-b) 0 with true => a::t | false => b::a::t end
    | false => a::b::t end
  end.
End IncorrectMerge.

Ltac merge_closed_value := arithmetic_closed_value.
Ltac type_merge :=
  first [solve [merge_closed_value] |
  lazymatch goal with
  | |- tm_has_type ?G ?e ?T => let e' := eval vm_compute in e in change (tm_has_type G e' T)
  | |- value_has_type ?G ?v ?T => let v' := eval vm_compute in v in change (value_has_type G v' T)
  end;
  lazymatch goal with
  | |- tm_has_type _ (tret _) _ => apply TT_Ret; type_merge
  | |- tm_has_type ?G (tlete _ _) _ =>
    let atoms := arith_atoms G in eapply TT_Let with (L:=atoms);
    [type_merge|let x:=fresh "x" in let Hx:=fresh "Hx" in intros x Hx; type_merge]
  | |- tm_has_type _ (tapp _ _) _ => eapply TT_App; type_merge
  | |- tm_has_type _ (tprim ?op _) _ =>
    let sig:=eval cbv in (prim_op_type op) in
    lazymatch sig with (?A,?B) => eapply TT_Op with (arg_b:=A) (ret_b:=B); [reflexivity|type_merge] end
  | |- tm_has_type _ (tmatch _ _ _) _ => apply TT_Match; type_merge
  | |- tm_has_type _ (tcons _ _) _ => apply TT_ListCons; type_merge
  | |- tm_has_type ?G (tmatchlist _ _ _) _ =>
    let atoms:=arith_atoms G in eapply TT_ListMatch with (L:=atoms);
    [type_merge|type_merge|let h:=fresh "h" in let t:=fresh "t" in
      let Hh:=fresh "Hh" in let Ht:=fresh "Ht" in intros h t Hh Ht; type_merge]
  | |- value_has_type _ (vconst _) _ => apply VT_Const
  | |- value_has_type _ (vfvar _) _ => apply VT_FVar; lookup_arith_var
  | |- value_has_type ?G (vlam _ _) _ => let atoms:=arith_atoms G in
    eapply VT_Lam with (L:=atoms); let x:=fresh "x" in let Hx:=fresh "Hx" in intros x Hx; type_merge
  | |- value_has_type ?G (vfix _ _) _ => let atoms:=arith_atoms G in
    eapply VT_Fix with (L:=atoms); let x:=fresh "x" in let Hx:=fresh "Hx" in intros x Hx; type_merge
  end].


Lemma merge_value_basic Δ : value_has_type Δ IncorrectMerge.merge_value merge_basic_ty.
Proof. type_merge. Qed.
Ltac merge_closed_value ::=
  first [arithmetic_closed_value | solve [apply merge_value_basic]].
Lemma merge_body_basic Δ x y :
  Δ !! x = Some (TBase TList) -> Δ !! y = Some (TBase TList) ->
  tm_has_type Δ (IncorrectMerge.body (vfvar x) (vfvar y)) (TBase TList).
Proof. intros Hx Hy. assert (Hxdom : x ∈ dom Δ) by (apply elem_of_dom; eauto). assert (Hydom : y ∈ dom Δ) by (apply elem_of_dom; eauto). type_merge. Qed.
Lemma merge_call_basic xs ys : tm_has_type ∅ (IncorrectMerge.call xs ys) (TBase TList).
Proof. type_merge. Qed.
