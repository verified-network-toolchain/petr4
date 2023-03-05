Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Import Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Import Poulet4.P4light.Syntax.P4Int.
Import String.

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
Locate  P4Int.
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
      (const_rules: list (list Pattern.pat * s))
      (ctrl_plane_name: string)
      (key: list Expr.e)
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
End TopDecl.
