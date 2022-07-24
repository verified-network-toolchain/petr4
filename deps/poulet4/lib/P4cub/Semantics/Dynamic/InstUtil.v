From Poulet4.P4cub Require Import Syntax.AST Semantics.Climate.
Import String.

(* TODO:
   Likely mnay holes in this file
   need to be filled with
   some [P4light/Architecture/Target.v]
   environment. *)

(** Control plane table entries,
    essentially mapping tables to an action call. *)
(* TODO: replace this with
   [P4light/Architecture/Target.v] equivalent. *)
Section Entries.
  Variable V : Set. (** values. *)

  Definition entries : Set :=
    list (V * string (* match kind *)) (* table key *) ->
    list string (* action names *) ->
    string * Expr.args.
  
  (** Control plane tables. *)
  Definition ctrl: Set := Clmt.t string entries.
End Entries.
  
(** Table environment. *)
Definition tenv: Set :=
  Clmt.t
    string (** table name. *)
    (list (Expr.e * string) (** table key *)
     * list string) (** actions *).

(** Function declarations and closures. *)
Inductive fdecl: Set :=
| FDecl (fs : Clmt.t string fdecl) (** function closure *)
        (body : Stmt.s) (** function body *).

(** Function names to closures. *)
Definition fenv: Set := Clmt.t string fdecl.
  
(** Action declarations and closures. *)
Inductive adecl: Set :=
| ADecl
    (fs : fenv) (** function closure *)
    (actions : Clmt.t string adecl) (** action closure *)
    (* TODO: needs De Bruijn extern instance closure env. *)
    (body : Stmt.s) (** action body *).

(** Action names to closures. *)
Definition aenv: Set := Clmt.t string adecl.

Section Inst.
  Variable V : Set. (** values. *)

  (** Control instances and environment. *)
  Inductive cinst: Set :=
  | CInst
      (ϵ : list V) (** value closure *)
      (fs : fenv) (** function closure *)
      (cis : list cinst) (** control instance closure *)
      (tbls : tenv) (** table closure *)
      (actions : aenv) (** action closure *)
      (* TODO: needs a De Bruijn extern instance closure environment. *)
      (apply_blk : Stmt.s)  (** control instance apply block *).
  
  Definition cienv: Set := list cinst.
  
  (** Parser instances. *)
  Inductive pinst: Set :=
  | PInst
      (ϵ : list V) (** value closure *)
      (fs : fenv) (** function closure *)
      (pis : list pinst) (** parser instance closure *)
      (* TOOD: needs a De Bruijn extern instance closure *)
      (strt : Stmt.s) (** start state *)
      (states : list Stmt.s) (** other states *).
  
  Definition pienv: Set := list pinst.

  (** Closures for control,parser, & extern declarations.
      For instantiable declarations. *)
  Inductive top_decl_closure : Set :=
  | ControlDecl
      (cs : Clmt.t string top_decl_closure) (** control declaration closure *)
      (fs : fenv) (** function closure *)
      (cis : cienv) (** control instance closure *)
      (* TODO: needs a De Bruijn extern instance closure *)
      (body : Control.d) (** declarations inside control *)
      (apply_block : Stmt.s) (** apply block *)
  | ParserDecl
      (ps : Clmt.t string top_decl_closure) (** parser declaration closure *)
      (fs : fenv) (** function closure *)
      (pis : pienv) (** parser instance closure *)
      (* TOOD: needs a De Bruijn extern instance closure *)
      (strt : Stmt.s) (** start state *)
      (states : list Stmt.s) (** parser states *)
  | ExternDecl
      (es : Clmt.t string top_decl_closure)
      (fs : fenv) (** function closure *)
  (* TOOD: needs a De Bruijn extern instance closure *).

  Definition top_decl_env: Set := Clmt.t string top_decl_closure.
End Inst.

Arguments CInst {_}.
Arguments PInst {_}.
Arguments ControlDecl {_}.
Arguments ParserDecl {_}.
Arguments ExternDecl {_}.