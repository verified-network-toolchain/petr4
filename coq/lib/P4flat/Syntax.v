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
Module Exp := CUB.Exp.

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
Module Stm.

  (** Statements. *)
  (* This datatype is mostly like CUB.Stm.t, but without
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
  Inductive t : Set :=
  | Skip                          (** skip/no-op *)
  | Ret (e : option Exp.t)    (** return *)
  | Exit                          (** exit *)
  | Asgn (lhs rhs : Exp.t)     (** assignment *)
  | SetValidity (validity : bool) (hdr : Exp.t) (** set a header [hdr]'s validity to [validity] *)
  | Invoke
      (lhs : option Exp.t)
      (ctrl_plane_name: string)
      (key: list Exp.t)
      (actions: list (string * Exp.args * t))
  | AppMethod
      (extern_instance_name : string)
      (method_name : string)
      (type_args : list Typ.t)
      (returns : option Exp.t)
      (args : Exp.args)
  (** blocks of statements: *)
  | LetIn
      (original_name : string)
      (init : Exp.t (** unitialized decl *) + Exp.t (** initialzed decl *))
      (tail : t) (** variable declaration/initialization
                     a let-in operator. *)
  | Seq (head tail : t) (** sequenced blocks,
                            variables introduced in [head]
                            do not occur in [tail] *)
  | Cond (guard : Exp.t)
      (tru fls : t) (** conditionals *)
  .
End Stm.

(** Top-Level Declarations *)
Module Top.
  
  (** Top-level declarations. *)
  Variant t : Set :=
    | Extern
        (extern_name : string)
        (type_params : nat)
        (cparams : CUB.Top.constructor_params)
        (expr_cparams : list Typ.t)
        (methods : Field.fs
                     string         (** method name *)
                     (nat           (** type parameters *)
                      * list string (** extern parameters *)
                      * CUB.Typ.arrowT (** parameters *)))
    (* Top-level blocks, to be included in packages. *)
    | ControlBlock
        (name : string)
        (eparams : list (string * string))
        (params: CUB.Typ.params)
        (body : Stm.t)
    | ParserBlock
        (name : string)
        (eparams : list (string * string))      (** runtime extern params *)
        (params : Typ.params)              (** invocation params *)
        (start : Stm.t) (** start state *)
        (states : list Stm.t) (** parser states *)
    (* Instantiations of packages. *)
    | Pkg (name: string) (cargs: list string).

  (** A p4flat program. *)
  Definition prog : Set := list t.

  Definition t_name (decl: t) : string :=
    match decl with
    | Extern name _ _ _ _
    | ControlBlock name _ _ _
    | ParserBlock name _ _ _ _
    | Pkg name _ => name
    end.

  Definition expect_extern (decl: t) :=
    match decl with
    | Extern extern_name type_params cparams expr_cparams methods =>
        ok (extern_name, type_params, cparams, expr_cparams, methods)
    | _ => error "got other decl"
    end.

  Definition expect_controlblock (decl: t) : result string (string * list (string * string) * CUB.Typ.params * Stm.t) :=
    match decl with
    | ControlBlock name eparams params body => ok (name, eparams, params, body)
    | _ => error "got other decl"
    end.
  
  Definition expect_pkg (decl: t) : result string (string * list string) :=
    match decl with
    | Pkg name cargs => ok (name, cargs)
    | _ => error "got other decl"
    end.

  Fixpoint find_decl (name: string) (p: prog) : result string t :=
    match p with
    | decl :: p' =>
        if String.eqb (t_name decl) name
        then ok decl
        else find_decl name p'
    | [] => error "decl not found"
    end.
  
End Top.
