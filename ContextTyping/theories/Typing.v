(** * ContextTyping.Typing

    Well-formedness predicates, auxiliary semantic relations, primitive
    operation signatures, and declarative typing rules for context types. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar Choice.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Import Context TypeDenote.
From Denotation Require Import TypeEquivTermBase TreeCoverage.
From ContextTyping Require Import PrimOpContext.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).

Open Scope ctx_scope.

(** * ContextTyping.WellFormed

    Paper-level well-formedness for context contexts and context types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  Semantic nonemptiness is not part of
    well-formedness: unsatisfiable contexts make the denotational soundness
    statement vacuous rather than unsound. *)


(** ** Context and type well-formedness *)

Definition wf_ctx_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  basic_ctx (dom Σ) Γ.

Definition wf_ctx (Γ : ctx) : Prop :=
  wf_ctx_under ∅ Γ.

Definition wf_context_ty (Γ : ctx) (τ : context_ty) : Prop :=
  wf_context_ty_at 0 (dom (⌊Γ⌋)%ctx) τ.

(** ** Semantic subtyping *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) : Prop :=
  let Δ := (⌊Γ⌋)%ctx in
  wf_ctx_under Σ Γ ∧
  wf_context_ty_at 0 (dom Δ) τ1 ∧
  wf_context_ty_at 0 (dom Δ) τ2 ∧
  (⌊τ1⌋)%cty = (⌊τ2⌋)%cty ∧
    ∀ e, Δ ⊢ₑ e ⋮ (⌊τ1⌋)%cty ->
    ⟦ctx Γ⟧[Σ] ⊫
      (TyDenote[Δ; τ1; e] → TyDenote[Δ; τ2; e])%formula.

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (⌊Γ1⌋)%ctx (⌊Γ2⌋)%ctx ∧
  ∀ r, r ⊨ ⟦ctx Γ1⟧[Σ] ->
       exists r',
         res_restrict r X ⊑ r' /\
         r' ⊨ ⟦ctx Γ2⟧[Σ].

(** ** Typing well-formedness side condition *)

Definition context_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (⌊Γ⌋)%ctx) τ /\
  (⌊Γ⌋)%ctx ⊢ₑ e ⋮ (⌊τ⌋)%cty.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  let Δ := (⌊Γ⌋)%ctx in
  ⟦ctx Γ⟧[Σ] ⊫
    (TyDenote[Δ; bool_precise_ty b; (ret v)%core] → ⊥)%formula.

(** The regular lemmas for these definitions live in [TypingRegular]. *)

Notation "Γ '⊢wf[' Σ ']' e '⋮' τ" :=
  (context_typing_wf Σ Γ e τ)
  (at level 40, Σ at level 200,
   e at level 200, τ at level 200).

Notation "Γ '⊢ᶜ' τ1 '≤[' Σ ']' τ2" :=
  (sub_type_under Σ Γ τ1 τ2)
  (at level 40, Σ at level 200,
   τ1 at level 200, τ2 at level 200).

Notation "Γ1 '≤ᶜ[' Σ ';' X ']' Γ2" :=
  (ctx_sub_under Σ X Γ1 Γ2)
  (at level 40, Σ at level 200, X at level 200,
   Γ2 at level 200).

Notation "'unreachable[' Σ ';' Γ ']' v '@' b" :=
  (branch_unreachable Σ Γ v b)
  (at level 40, Σ at level 200, Γ at level 200,
   v at level 200, b at level 200).

Reserved Notation "Γ '⊢ᶜ' '[' Φ ';' Σ ']' e '⋮' τ"
  (at level 40, Φ at level 200, Σ at level 200,
   e at level 200, τ at level 200).

(** A finite logical cover of contexts.  Unlike [CtxSum], this does not
    require every alternative to have a nonempty model simultaneously. *)
Fixpoint ctx_cases_denote (Σ : gmap atom ty) (cases : list ctx) : FormulaT :=
  match cases with
  | nil => FFalse
  | Γ :: rest => FOr (ctx_denote_under Σ Γ) (ctx_cases_denote Σ rest)
  end.

Inductive has_context_type (Φ : primop_ctx) (Σ : gmap atom ty) : ctx -> tm -> context_ty -> Prop :=

  (** T-Var *)
  | CT_Var x τ :
      ((x ∷ τ) ⊢wf[Σ] (ret (vfvar x))%core ⋮ τ) ->
      (x ∷ τ) ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      (Emp ⊢wf[Σ] (ret (vconst c))%core ⋮ (const_precise_ty c)) ->
      Emp ⊢ᶜ [Φ; Σ] (ret (vconst c))%core ⋮ const_precise_ty c

  (** T-Sub *)
  | CT_Sub Γ e (τ1 τ2 : context_ty) :
      (Γ ⊢wf[Σ] e ⋮ τ2) ->
      (Γ ⊢ᶜ [Φ; Σ] e ⋮ τ1) ->
      (Γ ⊢ᶜ τ1 ≤[Σ] τ2) ->
      Γ ⊢ᶜ [Φ; Σ] e ⋮ τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      (Γ1 ⊢wf[Σ] e ⋮ τ) ->
      (Γ2 ⊢ᶜ [Φ; Σ] e ⋮ τ) ->
      (Γ1 ≤ᶜ[Σ; (fv_tm e ∪ fv_cty τ)] Γ2) ->
      Γ1 ⊢ᶜ [Φ; Σ] e ⋮ τ

  (** T-PersistIntro.  Persistency introduction is value-only: arbitrary
      terms may have multiple possible results, while [ret v] exposes one
      result once the visible context resource is persistent. *)
  | CT_PersistIntro Γ v τ :
      (Γ ⊢wf[Σ] (ret v)%core ⋮ (□ τ)%cty) ->
      persistent_formula (ctx_denote_under Σ Γ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret v)%core ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (ret v)%core ⋮ (□ τ)%cty

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      (Γ ⊢wf[Σ] (let: e1 in e2)%core ⋮ τ2) ->
      (Γ ⊢ᶜ [Φ; Σ] e1 ⋮ τ1) ->
      (∀ x, x ∉ L ->
        ((Γ ,, (x ∷ τ1)) ⊢ᶜ [Φ; Σ] (e2 ^^ x) ⋮ τ2)) ->
      Γ ⊢ᶜ [Φ; Σ] (let: e1 in e2)%core ⋮ τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      ((Γ1 ∗ Γ2) ⊢wf[Σ] (let: e1 in e2)%core ⋮ τ2) ->
      (Γ1 ⊢ᶜ [Φ; Σ] e1 ⋮ τ1) ->
      (∀ x, x ∉ L ->
        ((Γ2 ∗ (x ∷ τ1)) ⊢ᶜ [Φ; Σ] (e2 ^^ x) ⋮ τ2)) ->
      (Γ1 ∗ Γ2) ⊢ᶜ [Φ; Σ] (let: e1 in e2)%core ⋮ τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      (Γ ⊢wf[Σ] (ret (λ: (⌊τx⌋)%cty, e))%core ⋮ (τx → τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ,, (y ∷ τx)) ⊢ᶜ [Φ; Σ] (e ^^ y) ⋮ ({0 ~> y} τ))) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (λ: (⌊τx⌋)%cty, e))%core ⋮
        (τx → τ)%cty

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      (Γ ⊢wf[Σ] (ret (λ: (⌊τx⌋)%cty, e))%core ⋮ (τx -∗ τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ∗ (y ∷ τx)) ⊢ᶜ [Φ; Σ] (e ^^ y) ⋮ ({0 ~> y} τ))) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (λ: (⌊τx⌋)%cty, e))%core ⋮
        (τx -∗ τ)%cty

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      (Γ ⊢wf[Σ] (v1 · vfvar x)%core ⋮ ({0 ~> x} τ)) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      (Γ ⊢ᶜ [Φ; Σ] (ret v1)%core ⋮ (τx → τ)%cty) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τx) ->
      Γ ⊢ᶜ [Φ; Σ] (v1 · vfvar x)%core ⋮ {0 ~> x} τ

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      ((Γ1 ∗ Γ2) ⊢wf[Σ] (v1 · vfvar x)%core ⋮ ({0 ~> x} τ)) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      (Γ1 ⊢ᶜ [Φ; Σ] (ret v1)%core ⋮ (τx -∗ τ)%cty) ->
      (Γ2 ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τx) ->
      (Γ1 ∗ Γ2) ⊢ᶜ [Φ; Σ] (v1 · vfvar x)%core ⋮ {0 ~> x} τ

  (** T-Fix *)
  | CT_Fix Γ φx τ vf b t (L : aset) :
      (⌊τ⌋)%cty = t ->
      (Γ ⊢wf[Σ]
        (ret (fix: (TBase b →ₜ t), vf))%core
        ⋮ (over_ty b φx → τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ,, (y ∷ over_ty b φx)) ⊢ᶜ [Φ; Σ]
          (ret ({0 ~> vfvar y} vf))%core
          ⋮ (fix_rec_call_ty b y (over_ty b φx) τ → {0 ~> y} τ)%cty)) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (fix: (TBase b →ₜ t), vf))%core ⋮
        (over_ty b φx → τ)%cty

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      (Γ ⊢wf[Σ]
        (tprim op (vfvar x))
        ⋮ ({0 ~> x} (primop_result_ty (Φ op)))) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ primop_arg_ty (Φ op)) ->
      Γ ⊢ᶜ [Φ; Σ] (tprim op (vfvar x)) ⋮ ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf x τt τf et ef :
      ((Γt ⊕ Γf) ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ (τt ⊕ τf)%cty) ->
      (Γt ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty true) ->
      (Γf ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty false) ->
      (Γt ⊢ᶜ [Φ; Σ] et ⋮ τt) ->
      (Γf ⊢ᶜ [Φ; Σ] ef ⋮ τf) ->
      (Γt ⊕ Γf) ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ (τt ⊕ τf)%cty

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ x τ et ef :
      (Γ ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ τ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty true) ->
      (Γ ⊢ᶜ [Φ; Σ] et ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ x τ et ef :
      (Γ ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ τ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty false) ->
      (Γ ⊢ᶜ [Φ; Σ] ef ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ τ

  (** T-VarR.  The final additive binding may depend on the prefix. *)
  | CT_VarR Γ x τ :
      ((Γ ,, (x ∷ τ)) ⊢wf[Σ] (ret (vfvar x))%core ⋮ τ) ->
      (Γ ,, (x ∷ τ)) ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τ

  (** T-VarSelf.  Returning a base variable has exactly that variable's
      value.  The well-formedness premise also checks its base type. *)
  | CT_VarSelf Γ x b :
      (Γ ⊢wf[Σ] (ret (vfvar x))%core ⋮
        precise_ty b (mk_q_eq (vbvar 0) (vfvar x))) ->
      Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮
        precise_ty b (mk_q_eq (vbvar 0) (vfvar x))

  (** T-CtxCases.  Check the same term and result type under a finite
      logical cover.  Each alternative has the same erased environment;
      coverage is disjunction, rather than the resource sum [CtxSum]. *)
  | CT_CtxCases Γ cases e τ :
      (Γ ⊢wf[Σ] e ⋮ τ) ->
      (forall Δ, In Δ cases -> erase_ctx Δ = erase_ctx Γ) ->
      (forall Δ, In Δ cases -> Δ ⊢ᶜ [Φ; Σ] e ⋮ τ) ->
      (ctx_denote_under Σ Γ ⊫ ctx_cases_denote Σ cases) ->
      Γ ⊢ᶜ [Φ; Σ] e ⋮ τ

  (** Conversion preserves both per-store results and must termination.
      It transports an existing derivation; it cannot introduce a type
      merely from an execution-correctness certificate. *)
  | CT_Conv Γ e1 e2 τ :
      (Γ ⊢wf[Σ] e2 ⋮ τ) ->
      (Γ ⊢ᶜ [Φ; Σ] e1 ⋮ τ) ->
      (forall m, m ⊨ ctx_denote_under Σ Γ ->
        tm_equiv_on m e1 e2 /\ tm_total_equiv_on m e1 e2) ->
      Γ ⊢ᶜ [Φ; Σ] e2 ⋮ τ

  (** Value eta introduction: every application is checked by a genuine
      derivation.  In particular this can check a closed fixed point by
      induction on its natural input, without an unconstrained self world. *)
  | CT_ArrowIntro Γ v b φ τ (L : aset) :
      (Γ ⊢wf[Σ] (ret v)%core ⋮ (over_ty b φ → τ)%cty) ->
      (forall x, x ∉ L ->
        (Γ ,, (x ∷ over_ty b φ)) ⊢ᶜ [Φ; Σ]
          (tapp_tm (tret v) (vfvar x)) ⋮ (cty_open 0 x τ)) ->
      Γ ⊢ᶜ [Φ; Σ] (ret v)%core ⋮ (over_ty b φ → τ)%cty

  (** Fiber classification.  Unlike finite logical context cases, this
      splits a world into fibers.  The result must explicitly be joinable;
      each fiber must satisfy one of the checked contexts. *)
  | CT_FiberCases (I : Type) Γ (cases : I -> ctx) X e τ :
      (Γ ⊢wf[Σ] e ⋮ τ) ->
      (forall n, erase_ctx (cases n) = erase_ctx Γ) ->
      (forall n, cases n ⊢ᶜ [Φ; Σ] e ⋮ τ) ->
      fiberwise_joinable_on X (ty_denote_under Σ Γ τ e) ->
      (forall m, m ⊨ ctx_denote_under Σ Γ ->
        forall σ mfib, res_fiber_from_projection m X σ mfib ->
          exists n, mfib ⊨ ctx_denote_under Σ (cases n)) ->
      Γ ⊢ᶜ [Φ; Σ] e ⋮ τ

  (** Adding a terminating branch preserves under coverage supplied by the
      right branch.  Both premises are genuine syntax derivations. *)
  | CT_ChooseUnder Γ left right b φ :
      (Γ ⊢wf[Σ] choose_tm left right ⋮ CTUnder b φ) ->
      (Γ ⊢ᶜ [Φ; Σ] left ⋮ CTOver b qual_top) ->
      (Γ ⊢ᶜ [Φ; Σ] right ⋮ CTUnder b φ) ->
      Γ ⊢ᶜ [Φ; Σ] choose_tm left right ⋮ CTUnder b φ

  (** A deterministic root graph combines conditional pivot/left/right
      coverage.  The certificate contains only pure qualifier conditions. *)
  | CT_NodeUnderGraph Γ S xp xk xl xr φP φK φL φR Θ
      (P : Store (V:=value) -> nat -> Prop)
      (K : Store (V:=value) -> nat -> nat -> Prop)
      (L : Store (V:=value) -> nat -> tree -> Prop)
      (R : Store (V:=value) -> nat -> tree -> tree -> Prop)
      (Q : Store (V:=value) -> tree -> Prop) :
      (Γ ⊢wf[Σ] tnode (vfvar xk) (vfvar xl) (vfvar xr) ⋮ CTUnder TTree Θ) ->
      node_under_graph_spec S xp xk xl xr φP φK φL φR Θ P K L R Q ->
      (Γ ⊢ᶜ [Φ; Σ] tret (vfvar xp) ⋮ CTUnder TNat φP) ->
      (Γ ⊢ᶜ [Φ; Σ] tret (vfvar xk) ⋮ CTOver TNat φK) ->
      (Γ ⊢ᶜ [Φ; Σ] tret (vfvar xl) ⋮ CTUnder TTree φL) ->
      (Γ ⊢ᶜ [Φ; Σ] tret (vfvar xr) ⋮ CTUnder TTree φR) ->
      Γ ⊢ᶜ [Φ; Σ] tnode (vfvar xk) (vfvar xl) (vfvar xr) ⋮ CTUnder TTree Θ

where "Γ ⊢ᶜ [ Φ ; Σ ] e ⋮ τ" := (has_context_type Φ Σ Γ e τ).

#[global] Hint Constructors has_context_type : core.
