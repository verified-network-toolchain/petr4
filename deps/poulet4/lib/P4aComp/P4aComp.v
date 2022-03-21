From Leapfrog Require Import Syntax Notations Ntuple.
From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Utils Require Import FinType P4Arith.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Module P4c := AST.
Module P4a := Syntax.
(* Open Scope p4a. *)

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
(* Want to crash if untranslatable *)
(* Fixpoint collect_hdrs (prog: P4c.TopDecl.d tags_t) : list (H * nat) :=
  match prog with 
    | TopDecl.TPParser p _ eps params st states i => [] ++ []
    | TopDecl.TPSeq d1 d2 _ => collect_hdrs d1 ++ collect_hdrs d2
    | _ => []
  end. *)


Fixpoint type_size (ctxt:F.fs string nat) (e:Expr.t) : option nat:=
  match e with 
    | Expr.TBool => Some 1
    | Expr.TBit n => Some (N.to_nat n)
    | Expr.TInt w => Some (Pos.to_nat w)
    | Expr.THeader fields => 
      List.fold_left (fun accum f => 
        match accum, f with 
          | (Some t1), (_, t2) => 
            match type_size ctxt t2 with 
              | Some field_size => Some (t1 + field_size)
              | _ => None
            end
          | _, _ => None
        end) fields (Some 0)
    | Expr.TTuple types => None  (* ? *)
    | Expr.TVar var_name => Field.find_value (String.eqb var_name) ctxt
    | _ => None
  end.
Check inl.

Fixpoint collect_hdrs_stmt (ctxt:F.fs string nat) (st: P4c.Stmt.s tags_t) : F.fs string nat :=
  match st with 
    | Stmt.SVardecl x expr _ => 
      match expr with 
        | inl typ => [prod x (type_size typ)] 
        | inr e => [prod x (0)] 
      end
    | Stmt.SSeq s1 s2 _ => collect_hdrs_stmt (collect_hdrs_stmt ctxt s1) s2
    | _ => ctxt
  end.

(* Fixpoitn collect_hdrs_state (state: ) :  *)

Fixpoint collect_hdrs (prog: P4c.TopDecl.d tags_t) : list (prod string nat) :=
  match prog with 
    | TopDecl.TPParser p _ eps params st states i => [] ++ []
    | TopDecl.TPSeq d1 d2 _ => collect_hdrs d1 ++ collect_hdrs d2
    | _ => []
  end.

Definition mk_hdr_type (hdrs: list (prod string nat)) : Type := Fin.t (List.length hdrs).













(* Notes: F.fs is an association list *)
(* Does not handle subparsers, for now consider only one parser *)

(* Inductive mk_hdr_type (parser: P4cubparser) : Type :=
| Hdr: forall id sz, List.In (id, sz) (collect_headers parser) -> mk_hdr_type parser.
Definition mk_hdr_sz (parser: P4cubparser) : mk_hdr_type parser -> nat.
Admitted. *)

(* Fixpoint translate_st (s:Stmt.s tags_t): op _:= 
  match s with 
  | Stmt.SSkip i => OpNil _
  | Stmt.SSeq s1 s2 i => OpNil
  | Stmt.SBlock s => OpNil
  | _ => OpNil
  end. *)
(* Fixpoint translate_state () *)

(* Fixpoint translate_trans (e:Parser.e) : transition
  match e with 
    | PGoto st i => TGoto (translate_state st)
    | PSelet discriminee default cases i =?>
  end. *)

Fixpoint get_parser (prog: P4c.TopDecl.d tags_t) : list (Parser.state_block tags_t) :=
  match prog with 
    | TopDecl.TPParser p _ eps params st states i => [st] ++ []
    | TopDecl.TPSeq d1 d2 _ => get_parser d1 ++ get_parser d2
    | _ => []
  end.

End P4AComp.

(* Fixpoint translate_parser (prog: P4c.TopDecl.d tags_t) :  *)

(* Fixpoint collect_hdrs_prog (prog : P4c.TopDecl.d tags_t) : list (H * nat) :=
  match prog with
  | TopDecl.TPInstantiate c_name i_name type_args cargs i => 
  | TopDecl.TPSeq d1 d2 _ => (collect_hdrs_prog d1) ++ (collect_hdrs_prog d2)
  | _ => []
  end.

(* Function find_hdr_size () *)

Function collect_hdrs (parser: P4c.Expr.ct) : list H * nat) := 
  match parser with 
  | _ => []
  end. *)

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