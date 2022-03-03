Require Export Poulet4.P4automata.Syntax.
(* Require Export Poulet4.P4cub.Syntax.AST. *)
Require Import Poulet4.Utils.FinType.

From Poulet4 Require Export P4cub.Syntax.AST
     P4cub.Syntax.CubNotations
     P4cub.Syntax.IndPrincip
     P4cub.Syntax.Equality
     P4cub.Syntax.Auxilary
     P4cub.Syntax.InferMemberTypes
     P4cub.Syntax.Occurs
     P4cub.Syntax.P4Field
     P4cub.Syntax.Substitution.
Module P4c := AST.
Module P4a := Syntax.
(* Print P4a.H. *)

Section P4AComp. 
  (* State identifiers. *)
Variable (S: Type).
Context `{S_eq_dec: EquivDec.EqDec S eq}.
Context `{S_finite: @Finite S _ S_eq_dec}.

(* Header identifiers. *)
Variable (H: Type).
Context `{H_eq_dec: EquivDec.EqDec H eq}.
Context `{H_finite: @Finite H _ H_eq_dec}.

Variable (tags_t : Type).

  Fixpoint collect_hdrs_prog (prog : P4c.TopDecl.d tags_t) : list (H * nat) :=
  match prog with
  | TPParser _ _ _ _ start states _ => []
  | TPSeq d1 d2 _ => (collect_hdrs_prog d1) ++ (collect_hdrs_prog d2)
  | _ => []
  end.
end. 
  (* Function collect_hdrs (parser: P4c.Expr.ct) : list (H * nat) :=
    match parser with
    | 
    end. *)

(* Axiom P4cubparser: Type.
Axiom ident: Type.

Definition collect_headers (parser: P4cubparser) : list (ident * nat).
Admitted.
Definition collect_states (parser: P4cubparser) : list ident.
Admitted.

Inductive mk_hdr_type (parser: P4cubparser) : Type :=
| Hdr: forall id sz, List.In (id, sz) (collect_headers parser) -> mk_hdr_type parser.
Definition mk_hdr_sz (parser: P4cubparser) : mk_hdr_type parser -> nat.
Admitted.
Definition mk_st (parser: P4cubparser) : Type.
Admitted.

Definition mk_states (parser: P4cubparser): mk_st parser -> state (mk_st parser) (mk_hdr_sz parser).
Admitted. *)