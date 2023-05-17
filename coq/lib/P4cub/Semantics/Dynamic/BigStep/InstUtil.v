From Poulet4.P4cub Require Import
  Syntax.AST Semantics.Climate Semantics.Dynamic.BigStep.Value.Syntax.
From RecordUpdate Require Import RecordSet.
Import String Clmt.Notations RecordSetNotations.

Module Table.
  Record t : Set :=
    mk_t
      { scope : nat (** number of variables in scope. Tables have dynamic scope. *);
        key : list (Exp.t * string);
        actions : list (string * Exp.args);
        default : option (string * list Exp.t)
      }.

  Global Instance eta_t : Settable _ :=
    settable! mk_t <scope; key; actions; default>.
End Table.

(** Table environment. *)
Definition table_env : Set :=
  Clmt.t string (** table name. *) Table.t.

(** Function declarations and closures. *)
Inductive fdecl: Set :=
| FDecl (fs : Clmt.t string fdecl) (** function closure *)
        (params : Typ.params)
        (body : Stm.t).

(** Function names to closures. *)
Definition fenv: Set := Clmt.t string fdecl.
  
(** Action declarations and closures. *)
Inductive adecl: Set :=
| ADecl
    (clos : list Val.t) (** value closure *)
    (actions : Clmt.t string adecl) (** action closure *)
    (ctrl_params : list Typ.t) (** control-plane parameters *)
    (data_params : Typ.params) (** data-plane parameters *)
    (body : Stm.t).

(** Action names to closures. *)
Definition aenv: Set := Clmt.t string adecl.

Section Inst.
  Context {V : Set}. (** values. *)

  (** Instances and environment. *)
  Inductive inst: Set :=
  | ControlInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (tbls : table_env) (** table closure *)
      (actions : aenv) (** action closure *)
      (vs : list V) (** constructor args *)
      (params : Typ.params)
      (apply_blk : Stm.t)  (** control instance apply block *)
  | ParserInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (vs : list V) (** constructor args *)
      (params : Typ.params)
      (strt : Stm.t) (** start state *)
      (states : list Stm.t) (** other states *)
  | ExternInst
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (vs : list V) (** constructor args *).
  (* TODO: what else? *)
  
  Definition inst_env: Set := Clmt.t string inst.

  Definition bind_constructor_args
    (cparams : list string)
    (cargs : Top.constructor_args)
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
  Inductive top_closure : Set :=
  | ControlDecl
      (fs : fenv) (** function closure *)
      (insts : inst_env) (** control instance closure *)
      (cparams : list string) (** constructor param names *)
      (params : Typ.params)
      (body : list Ctrl.t) (** declarations inside control *)
      (apply_block : Stm.t) (** apply block *)
  | ParserDecl
      (fs : fenv) (** function closure *)
      (insts : inst_env) (** parser instance closure *)
      (cparams : list string) (** constructor param names *)
      (params : Typ.params)
      (strt : Stm.t) (** start state *)
      (states : list Stm.t) (** parser states *)
  | ExternDecl
      (fs : fenv) (** function closure *)
      (insts : Clmt.t string inst) (** instance closure *)
      (cparams : list string) (** constructor param names *).

  Definition top_env: Set := Clmt.t string top_closure.
End Inst.

Arguments inst : clear implicits.
Arguments inst_env : clear implicits.
Arguments top_closure : clear implicits.
Arguments top_env : clear implicits.
