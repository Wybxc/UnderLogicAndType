(** * Section4Extension specification types

    Extracted from CaseStudy/theories/Section4Extension.v at cd3eace.
    Program terms, typing derivations, and subtyping obligations are omitted. *)

From CaseStudy Require Import CaseTypes.

Open Scope core_scope.
Open Scope cty_scope.

Definition bool_to_nat_ty : ty := (𝔹 : ty) →ᵦ ℕ.

Definition bool_to_bool_ty : ty := (𝔹 : ty) →ᵦ 𝔹.
