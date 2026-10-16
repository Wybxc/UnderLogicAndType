(** * Section1Intro specification types

    Extracted from CaseStudy/theories/Section1Intro.v at cd3eace.
    Program terms, typing derivations, and subtyping obligations are omitted. *)

From CaseStudy Require Import CaseTypes.

Open Scope core_scope.
Open Scope cty_scope.

Definition nat_minus_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ ℕ.

Definition unary_nat_fun_ty : ty :=
  ℕ →ᵦ ℕ.

Definition higher_order_apply_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ.
