Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Import Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Import Poulet4.P4light.Syntax.P4Int.
Require Import Poulet4.Monads.Result.
Import String.

Local Open Scope string_scope.

(** * P4flat AST *)

(* We reuse P4cub expressions and expression types. *)
Module CUB := P4cub.Syntax.AST.
Module Expr := CUB.Expr.

Module Lval.
  Inductive lv :=
  | Var (v: string)
  | Index (array : lv) (index : nat)
  | Member (struct: lv) (field : nat).
End Lval.

Module Pattern.
  Inductive pat : Set :=
  | Wild                         (** wild-card/anything pattern *)
  | Mask  (p1 p2 : P4Int.t unit) (** mask pattern *)
  | Range (p1 p2 : P4Int.t unit) (** range pattern *)
  | Exact (i : P4Int.t unit)     (** exact pattern *)
  | Prod (ps : list pat)         (** product pattern *).
End Pattern.

(** * Statement and Block Grammar *)
Module Stmt.

  (** Statements. *)
  (* This datatype is mostly like CUB.Stmt.s, but without
     any calls to
        - functions,
        - actions,
        - controls,
        - or parsers,
     all of which should be inlined. Tables are inlined at their call
     site as a special Table statement. The table statement includes a
     control plane name so that multiple inlined copies of the same
     table may share control-plane state. Extern calls are left
     unchanged. *)
  Inductive s : Set :=
  | Skip                          (** skip/no-op *)
  | Return (e : option Expr.e)    (** return *)
  | Exit                          (** exit *)
  | Assign (lhs rhs : Expr.e)     (** assignment *)
  | ExternCall
      (extern_instance_name : string)
      (method_name : string)
      (type_args : list Expr.t)
      (args : Expr.args)
      (returns : option Expr.e)
  | Table
      (ctrl_plane_name: string)
      (key: list Expr.e)
      (actions: list (string * s))
  (** blocks of statements: *)
  | Var
      (original_name : string)
      (expr : Expr.t (** unitialized decl *) + Expr.e (** initialzed decl *))
      (tail : s) (** variable declaration/initialization
                     a let-in operator. *)
  | Seq (head tail : s) (** sequenced blocks,
                            variables introduced in [head]
                            do not occur in [tail] *)
  | Conditional (guard : Expr.e)
      (tru_blk fls_blk : s) (** conditionals *).
End Stmt.

(** Top-Level Declarations *)
Module TopDecl.
  
  (** Top-level declarations. *)
  Variant d : Set :=
    | Extern
        (extern_name : string)
        (type_params : nat)
        (cparams : CUB.TopDecl.constructor_params)
        (expr_cparams : list Expr.t)
        (methods : Field.fs
                     string         (** method name *)
                     (nat           (** type parameters *)
                      * list string (** extern parameters *)
                      * Expr.arrowT (** parameters *)))
    (* Top-level blocks, to be included in packages. *)
    | ControlBlock
        (name : string)
        (params: Expr.params)
        (body : Stmt.s)
    (* Instantiations of packages. *)
    | Pkg (name: string) (cargs: list string).

  (** A p4flat program. *)
  Definition prog : Set := list d.

  Definition d_name (decl: d) : string :=
    match decl with
    | Extern name _ _ _ _
    | ControlBlock name _ _
    | Pkg name _ => name
    end.

  Definition expect_extern (decl: d) :=
    match decl with
    | Extern extern_name type_params cparams expr_cparams methods =>
        ok (extern_name, type_params, cparams, expr_cparams, methods)
    | _ => error "got other decl"
    end.

  Definition expect_controlblock (decl: d) : result string (string * Expr.params * Stmt.s) :=
    match decl with
    | ControlBlock name params body => ok (name, params, body)
    | _ => error "got other decl"
    end.
  
  Definition expect_pkg (decl: d) : result string (string * list string) :=
    match decl with
    | Pkg name cargs => ok (name, cargs)
    | _ => error "got other decl"
    end.

  Fixpoint find_decl (name: string) (p: prog) : result string d :=
    match p with
    | decl :: p' =>
        if String.eqb (d_name decl) name
        then ok decl
        else find_decl name p'
    | [] => error "decl not found"
    end.
  
End TopDecl.
