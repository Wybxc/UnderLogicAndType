(** * MayMust specification types

    Extracted from CaseStudy/theories/MayMust.v at cd3eace.
    Program terms, typing derivations, and subtyping obligations are omitted. *)

From CaseStudy Require Import CaseTypes.

Open Scope core_scope.
Open Scope cty_scope.

Definition may_may_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition may_reach_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.

Definition q_nat_ge0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat <= n).

Definition q_nat_gt0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat < n).

Definition q_nat_ne0 : type_qualifier :=
  q_nat_pred ν (fun n => n <> 0%nat).

Definition q_nat_eq1 : type_qualifier :=
  q_nat_pred ν (fun n => n = 1%nat).

Definition may_may_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition may_may_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: 𝔹 | q_false }.

Definition may_may_ref_ty : context_ty :=
  may_may_g_ty → may_may_f_ty.

Definition must_may_g_ty : context_ty :=
  U[ ℕ ] → [: ℕ | q_nat_ge0 ].

Definition must_may_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: 𝔹 | q_true ].

Definition must_may_ref_ty : context_ty :=
  must_may_g_ty → must_may_f_ty.

Definition may_reach_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ne0 }.

Definition may_reach_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: ℕ | q_nat_eq1 ].

Definition may_reach_ref_ty : context_ty :=
  may_reach_g_ty → may_reach_f_ty.

Definition must_inter_g_ty : context_ty :=
  (O[ ℕ ] → {: ℕ | q_nat_gt0 }) ⊓
  (U[ ℕ ] → [: ℕ | q_nat_gt0 ]).

Definition must_inter_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition must_inter_ref_ty : context_ty :=
  must_inter_g_ty → must_inter_f_ty.

Definition comprehensive_inter_f_ty : context_ty :=
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ [: ℕ | q_nat_eq1 ]).
