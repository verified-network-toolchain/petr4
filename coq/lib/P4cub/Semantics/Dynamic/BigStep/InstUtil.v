From Poulet4.P4cub Require Import
  Syntax.AST Semantics.Climate Semantics.Dynamic.BigStep.Value.Syntax.
Import String Clmt.Notations.
  
(** Table environment. *)
Definition tenv : Set :=
  Clmt.t
    string (** table name. *)
    (nat (** number of variables in scope. Tables have dynamic scope. *)
     * list (Expr.e * string) (** table key. *)
     * list (string * Expr.args) (** actions. *)
     * option (string * list Expr.e)) (** default action. *).

(** Function declarations and closures. *)
Inductive fdecl: Set :=
| FDecl (fs : Clmt.t string fdecl) (** function closure *)
        (body : Stmt.s) (** function body *).

(** Function names to closures. *)
Definition fenv: Set := Clmt.t string fdecl.
  
(** Action declarations and closures. *)
Inductive adecl: Set :=
| ADecl
    (clos : list Val.v) (** value closure *)
    (actions : Clmt.t string adecl) (** action closure *)
    (body : Stmt.s) (** action body *).

(** Action names to closures. *)
Definition aenv: Set := Clmt.t string adecl.

Section Inst.
  Context {V : Set}. (** values. *)

  (** Instances and environment. *)
  Inductive inst: Set :=
  | ControlInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (tbls : tenv) (** table closure *)
      (actions : aenv) (** action closure *)
      (epsilon : list V) (** constructor args *)
      (apply_blk : Stmt.s)  (** control instance apply block *)
  | ParserInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (epsilon : list V) (** constructor args *)
      (strt : Stmt.s) (** start state *)
      (states : list Stmt.s) (** other states *)
  | ExternInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (epsilon : list V) (** constructor args *)
  (* TODO: what else? *).
  
  Definition inst_env: Set := Clmt.t string inst.

  Definition bind_constructor_args
    (cparams : list string)
    (cargs : TopDecl.constructor_args)
    (instance_site closure : inst_env) : inst_env :=
    List.fold_right
      (fun '(param, arg) cls =>
         match instance_site arg with
         | None => cls
         | Some inst => (param ↦ inst ,, cls)%climate
         end)
      closure
      (List.combine cparams cargs).

  (** Closures for control,parser, & extern declarations.
      For instantiable declarations. *)
  Inductive top_decl_closure : Set :=
  | ControlDecl
      (fs : fenv) (** function closure *)
      (insts : inst_env) (** control instance closure *)
      (cparams : list string) (** constructor param names *)
      (body : list Control.d) (** declarations inside control *)
      (apply_block : Stmt.s) (** apply block *)
  | ParserDecl
      (fs : fenv) (** function closure *)
      (insts : inst_env) (** parser instance closure *)
      (cparams : list string) (** constructor param names *)
      (strt : Stmt.s) (** start state *)
      (states : list Stmt.s) (** parser states *)
  | ExternDecl
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (cparams : list string) (** constructor param names *)
  (** function closure *).

  Definition top_decl_env: Set := Clmt.t string top_decl_closure.
End Inst.

Arguments inst : clear implicits.
Arguments inst_env : clear implicits.
Arguments top_decl_closure : clear implicits.
Arguments top_decl_env : clear implicits.
