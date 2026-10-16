(** * Corrected Fig. 7 program and its target typing judgment

    [BSTGenerator] specifies a persistent, exact closed-interval range
    generator. This module encodes the Fig. 7 program in the existing core
    language. Arithmetic is implemented with recursive unary primitives;
    no binary primitives or context-typing rules are added here.

    [bst_gen_type_judgement] states the desired context-typing proposition.
    It is a definition, not a proof of a context-typing derivation. *)

From CaseStudy Require Export BSTGenerator.
From CaseStudy Require Import CaseTypes.
From CaseStudy Require Export NatArithmetic.
From CoreLang Require Import Sugar BasicTypingProps.
From ContextTyping Require Import Typing PrimOpConcreteContext.

Open Scope core_scope.
Open Scope cty_scope.

Module BSTProgram.

Include NatArithmetic.NatArithmetic.

Definition r : atom := 10%positive.
Definition lo : atom := 11%positive.
Definition range_arg : atom := 12%positive.
Definition rec : atom := 13%positive.
Definition isz : atom := 14%positive.
Definition pivot : atom := 15%positive.
Definition left_size : atom := 16%positive.
Definition right_size : atom := 17%positive.
Definition root : atom := 18%positive.
Definition left_tree : atom := 19%positive.
Definition right_tree : atom := 20%positive.

Definition range_basic_ty : ty := TNat →ᵦ TNat →ᵦ TNat.
Definition result_fun_ty : ty := TNat →ᵦ range_basic_ty →ᵦ TTree.

(**
    fix bst_gen r lo range =
      if r = 0 then Leaf else
      Leaf ⊕
        let p = range 1 r in
        let left_size = p - 1 in
        let right_size = r - p in
        let root = lo + p in
        let left = bst_gen left_size lo range in
        let right = bst_gen right_size root range in
        Node root left right

    The first fix argument is r; recursive self is a separate binder in
    the HAT-style [vfix] representation used by the core language. *)
Definition bst_gen : value :=
  fix_fun rec r TNat result_fun_ty
    (ret (lam lo TNat
      (ret (lam range_arg range_basic_ty
        (let_in isz (tprim op_eq0 (vfvar r))
          (tmatch (vfvar isz) (ret Leaf)
            (choose (ret Leaf)
              (let_in pivot
                (app2 (vfvar range_arg) (vnat 1) (vfvar r))
                (let_in left_size (tprim op_minus1 (vfvar pivot))
                  (let_in right_size
                    (app2 sub_value (vfvar r) (vfvar pivot))
                    (let_in root
                      (app2 add_value (vfvar lo) (vfvar pivot))
                      (let_in left_tree
                        (app3 (vfvar rec) (vfvar left_size)
                          (vfvar lo) (vfvar range_arg))
                        (let_in right_tree
                          (app3 (vfvar rec) (vfvar right_size)
                            (vfvar root) (vfvar range_arg))
                          (tnode (vfvar root) (vfvar left_tree)
                            (vfvar right_tree))))))))))))))).

End BSTProgram.

Definition bst_gen_value : value := BSTProgram.bst_gen.
Definition bst_gen_program : tm := tret bst_gen_value.

(** Target context-type judgment (proof deferred):

      Emp |- ret bst_gen :
        Box (r : ONat -> lo : ONat -> range : range_ty ->
          [t : tree | bst_spec r lo t])

    Here [range_ty] is the persistent closed-interval precise contract in
    [BSTGenerator]. [concrete_Φ] supplies the five existing unary primitive
    signatures; both the ambient store environment and the term context
    are empty. This definition records a proposition without assuming its
    derivability. A proof will need sound support for tree construction in
    context typing. *)
Definition bst_gen_type_judgement : Prop :=
  CtxEmpty ⊢ᶜ [concrete_Φ; ∅] bst_gen_program ⋮ bst_gen_ty.

Definition bst_gen_basic_type_judgement : Prop :=
  tm_has_type ∅ bst_gen_program bst_gen_basic_ty.

Lemma bst_gen_type_erasure : erase_ty bst_gen_ty = bst_gen_basic_ty.
Proof. reflexivity. Qed.

(** The proof below checks the actual closed core term, including the
    recursive arithmetic helpers, against the existing STLC rules. *)
Local Ltac bst_atoms G :=
  lazymatch G with
  | <[?x := _]> ?G' =>
      let L := bst_atoms G' in constr:({[x]} ∪ L : aset)
  | _ => constr:(∅ : aset)
  end.

Local Ltac lookup_bst_var :=
  lazymatch goal with
  | |- (<[?x := _]> _) !! ?y = _ =>
      tryif constr_eq x y then apply lookup_insert_eq else
      rewrite lookup_insert_ne by set_solver; lookup_bst_var
  | |- _ => fail "BST variable is missing from the basic typing context"
  end.

Local Ltac type_bst :=
  lazymatch goal with
  | |- tm_has_type ?G ?e ?T =>
      let e' := eval vm_compute in e in change (tm_has_type G e' T)
  | |- value_has_type ?G ?v ?T =>
      let v' := eval vm_compute in v in change (value_has_type G v' T)
  end;
  lazymatch goal with
  | |- tm_has_type _ (tret _) _ => apply TT_Ret; type_bst
  | |- tm_has_type ?G (tlete _ _) _ =>
      let atoms := bst_atoms G in
      eapply TT_Let with (L := atoms);
      [type_bst | let x := fresh "x" in let Hx := fresh "Hx" in
        intros x Hx; type_bst]
  | |- tm_has_type _ (tprim ?op _) _ =>
      let sig := eval cbv in (prim_op_type op) in
      lazymatch sig with
      | (?A, ?B) => eapply TT_Op with (arg_b := A) (ret_b := B);
          [reflexivity | type_bst]
      end
  | |- tm_has_type _ (tapp _ _) _ => eapply TT_App; type_bst
  | |- tm_has_type _ (tmatch _ _ _) _ => apply TT_Match; type_bst
  | |- tm_has_type _ (tnode _ _ _) _ => apply TT_TreeNode; type_bst
  | |- value_has_type _ (vconst _) _ => apply VT_Const
  | |- value_has_type _ (vfvar _) _ => apply VT_FVar; lookup_bst_var
  | |- value_has_type ?G (vlam _ _) _ =>
      let atoms := bst_atoms G in
      eapply VT_Lam with (L := atoms);
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; type_bst
  | |- value_has_type ?G (vfix _ _) _ =>
      let atoms := bst_atoms G in
      eapply VT_Fix with (L := atoms);
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; type_bst
  | |- _ => fail "Unsupported BST basic typing goal"
  end.

Lemma bst_gen_basic_typed : bst_gen_basic_type_judgement.
Proof.
  unfold bst_gen_basic_type_judgement, bst_gen_basic_ty.
  let e := eval vm_compute in bst_gen_program in
  change (tm_has_type ∅ e
    (TNat →ᵦ TNat →ᵦ (TNat →ᵦ TNat →ᵦ TNat) →ᵦ TTree)).
  type_bst.
Qed.

Lemma bst_gen_program_closed : fv_tm bst_gen_program = ∅.
Proof. eapply basic_typing_closed_tm; exact bst_gen_basic_typed. Qed.

Lemma bst_gen_program_locally_closed : lc_tm bst_gen_program.
Proof. eapply typing_tm_lc; exact bst_gen_basic_typed. Qed.
