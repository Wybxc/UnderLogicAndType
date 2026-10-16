(** * Case-study specification helpers

    Extracted from ProofAutomation/CaseTypes.v at cd3eace.  Only type aliases,
    qualifier constructors, and notation are included. *)

From Stdlib Require Import List.
From CoreLang Require Export SyntaxNotation.
From ContextTypeLanguage Require Export Syntax.

Import ListNotations.

Open Scope core_scope.
Open Scope cty_scope.

Notation "T1 '→ᵦ' T2" := (TArrow T1 T2)
  (at level 99, right associativity,
   format "T1  →ᵦ  T2") : core_scope.

Definition vnu : value := vbvar 0.

Definition arg0 : value := vbvar 1.

Definition arg1 : value := vbvar 2.

Definition arg2 : value := vbvar 3.

Definition arg3 : value := vbvar 4.

Definition nat_unary_fun_ty : ty :=
  ℕ →ᵦ ℕ.

Definition nat_binop_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ ℕ.

Definition nat_cmp_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition bool_binop_ty : ty :=
  𝔹 →ᵦ 𝔹 →ᵦ 𝔹.

Definition q_const_pred (v : value) (P : constant -> Prop) : type_qualifier :=
  tqual (lvar_value_keys v)
    (fun σ =>
       exists c,
         denote_lvar_value (lso_store σ) v = Some (vconst c) /\
         P c).

Definition q_nat_pred (v : value) (P : nat -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with cnat n => P n | _ => False end).

Definition q_bool_pred (v : value) (P : bool -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with cbool b => P b | _ => False end).

Definition q_true : type_qualifier := bool_qual true.

Definition q_false : type_qualifier := bool_qual false.

Definition q_nonneg (v : value) : type_qualifier :=
  q_nat_pred v (fun _ => True).

Definition ONat : context_ty := over_ty TNat qual_top.

Definition UNat : context_ty := under_ty TNat qual_top.

Definition OBool : context_ty := over_ty TBool qual_top.

Definition UBool : context_ty := under_ty TBool qual_top.

Definition precise_const (c : constant) : context_ty :=
  const_precise_ty c.

Notation "'ν'" := vnu : cty_scope.
Notation "'O[' b ']'" := (over_ty b qual_top)
  (at level 0, b at level 200, format "O[ b ]") : cty_scope.
Notation "'U[' b ']'" := (under_ty b qual_top)
  (at level 0, b at level 200, format "U[ b ]") : cty_scope.

Definition q_list_pred (v : value) (P : list nat -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with clist xs => P xs | _ => False end).

Definition q_tree_pred (v : value) (P : tree -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with ctree t => P t | _ => False end).

Definition OTree : context_ty := over_ty TTree qual_top.

Definition UTree : context_ty := under_ty TTree qual_top.

Definition OList : context_ty := over_ty TList qual_top.

Definition UList : context_ty := under_ty TList qual_top.
