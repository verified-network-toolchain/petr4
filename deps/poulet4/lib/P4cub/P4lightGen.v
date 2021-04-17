Require Import Poulet4.Syntax.
Require Import Poulet4.Typed.
Require Import Poulet4.P4cub.AST.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Info.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope type_scope.

Module P4lightGen.

Definition path := list string.

Inductive virloc :=
  | VLAbsolute (n  : path)  : virloc
  | VLObject (n  : path)  : virloc. (* name from the control or parser *)

Definition instantiation_expression := unit. (* TODO *)
(* Should contain name of the instance, and a closure-ish. *)

Definition decl_list := list (P4cub.TopDecl.d Info + instantiation_expression).
Definition state := decl_list * path.
Inductive exception :=
  | NotFound
  | Unimpletmented. (* unimplemented stub *)

Definition get_decl_list : (@state_monad state exception decl_list) :=
  fun s => let (ds, p) := s in (inl ds, (ds, p)).

Definition set_decl_list ds : (@state_monad state exception unit) :=
  fun s => let (_, p) := s in (inl tt, (ds, p)).

Definition get_path : (@state_monad state exception path) :=
  fun s => let (ds, p) := s in (inl p, (ds, p)).

Definition set_path p : (@state_monad state exception unit) :=
  fun s => let (ds, _) := s in (inl tt, (ds, p)).

Definition add_decl d : (@state_monad state exception unit) :=
  fun s => let (ds, p) := s in (inl tt, (ds ++ [d], p)).

Definition get_full_name n : (@state_monad state exception path) :=
  fun s => let (ds, p) := s in (inl (p ++ n), (ds, p)).

Definition unimplemented {A} : (@state_monad state exception A) :=
  fun s => (inr Unimpletmented, s).

Inductive X :=
  | Nil : X
  | Node : list X -> X.

Fixpoint f (x : X) : nat :=
  match x with
  | Nil => O
  | Node xs =>
    fold_left (fun acc x => Nat.add acc (f x)) xs O
  end.

Definition fold_left_monad {A B} (f : A -> B -> @state_monad state exception A) l acc :=
  fold_left (fun m x => acc <- m;; (f acc x)) l (mret acc).

(* Pass1: d esugerize nameless instantiation *)
Module Pass1.
  Definition environment := unit. (* TODO *)
  Definition tags_t := unit. (* Let's ignore tags. *)
  Definition empty_tag : tags_t := tt. (* Let's ignore tags. *)
  Notation P4String := (P4String.t tags_t).

  Definition fresh : (@state_monad state exception P4String) :=
    unimplemented. (* TODO *)

  Definition update_env (env : environment) (decls : list (@Declaration tags_t)) : (@state_monad state exception environment) :=
    unimplemented. (* TODO *)

  Fixpoint transExpr (env : environment) (expr : @Expression tags_t) : (@state_monad state exception (list (@Declaration tags_t) * @Expression tags_t)) :=
    match expr with
    | MkExpression _ epre _ _ =>
      match epre with
      (* | ExpBool (b : bool) => unimplemented
      | ExpInt (_ : P4Int) => unimplemented
      | ExpString (_ : P4String) => unimplemented
      | ExpName (_ : Typed.name tags_t) => unimplemented
      | ExpArrayAccess (array : Expression) (index : Expression) => unimplemented
      | ExpBitStringAccess (bits : Expression) (lo : N) (hi : N) => unimplemented
      | ExpList (value : list Expression) => unimplemented
      | ExpRecord (entries : list KeyValue) => unimplemented
      | ExpUnaryOp (op : OpUni) (arg : Expression) => unimplemented
      | ExpBinaryOp (op : OpBin) (args : (Expression * Expression)) => unimplemented
      | ExpCast (typ : P4Type tags_t) (expr : Expression) => unimplemented
      | ExpTypeMember (typ : Typed.name tags_t) (name : P4String) => unimplemented
      | ExpErrorMember (_ : P4String) => unimplemented
      | ExpExpressionMember (expr : Expression) (name : P4String) => unimplemented
      | ExpTernary (cond : Expression) (tru : Expression) (fls : Expression) => unimplemented
      | ExpFunctionCall (func : Expression) (type_args : list (P4Type tags_t))
                        (args : list (option Expression)) => unimplemented *)
      | ExpNamelessInstantiation typ args =>
          fresh_name <- fresh;;
          let* (env, decls, exprs) := fold_left_monad
              (fun (acc : environment * (list (@Declaration tags_t)) * (list (@Expression tags_t))) e =>
                  let (t1, exprs) := acc in let (env, decls) := t1 in
                  let* (decls1, expr1) := transExpr env expr in
                  (env' <- update_env env decls1;;
                  mret (env', decls ++ decls1, exprs ++ [expr1]))
              )
              args
              (env, [], []) in
          mret (decls ++
              [DeclInstantiation empty_tag typ exprs fresh_name None],
              MkExpression empty_tag (ExpName (BareName fresh_name)) typ Directionless)
      (* | ExpDontCare => unimplemented
      | ExpMask (expr : Expression) (mask : Expression) => unimplemented
      | ExpRange (lo : Expression) (hi : Expression) => unimplemented *)
      | _ => unimplemented
      end
    end.
End Pass1.

(* Inductive parser_closure := (* TODO *)
  .

Inductive control_closure := (* TODO *)
  .

Inductive object_closure :=
  | ParserClosure (pc : parser_closure)  : object_closure
  | ControlClosure (cc : control_closure)  : object_closure.







Fixpoint instantiate (oc : object_closure) (args : list Expression)  : TopDecl.d.

(* Stub to transform expression in Syntax.v to AST.v *)
Fixpoint transExpr (env : environment) (exp : Expression unit) : (@state_monad state exception (list Stmt.s * Expr.e)) :=
  match exp with
  | MkExpression _ epre _ _ =>
    match epre with
    | ExpBool (b : bool) => unimplemented
    | ExpInt (_ : P4Int) => unimplemented
    | ExpString (_ : P4String) => unimplemented
    | ExpName (_ : Typed.name tags_t) => unimplemented
    | ExpArrayAccess (array : Expression) (index : Expression) => unimplemented
    | ExpBitStringAccess (bits : Expression) (lo : N) (hi : N) => unimplemented
    | ExpList (value : list Expression) => unimplemented
    | ExpRecord (entries : list KeyValue) => unimplemented
    | ExpUnaryOp (op : OpUni) (arg : Expression) => unimplemented
    | ExpBinaryOp (op : OpBin) (args : (Expression * Expression)) => unimplemented
    | ExpCast (typ : P4Type tags_t) (expr : Expression) => unimplemented
    | ExpTypeMember (typ : Typed.name tags_t) (name : P4String) => unimplemented
    | ExpErrorMember (_ : P4String) => unimplemented
    | ExpExpressionMember (expr : Expression) (name : P4String) => unimplemented
    | ExpTernary (cond : Expression) (tru : Expression) (fls : Expression) => unimplemented
    | ExpFunctionCall (func : Expression) (type_args : list (P4Type tags_t))
                      (args : list (option Expression)) => unimplemented
    | ExpNamelessInstantiation (typ : P4Type tags_t) (args : list Expression) =>
        _ <- add_decl (instantiate env typ nil);; args
    | ExpDontCare => unimplemented
    | ExpMask (expr : Expression) (mask : Expression) => unimplemented
    | ExpRange (lo : Expression) (hi : Expression) => unimplemented
    end
  end.

Fixpoint transExp (env : environment) (exp : Expression unit) : (@state_monad state exception (list Stmt.s * Expr.e)) :=
  match exp with
  | MkExpression _ epre _ _ =>
    match epre with
    | ExpBool (b : bool) => unimplemented
    | ExpInt (_ : P4Int) => unimplemented
    | ExpString (_ : P4String) => unimplemented
    | ExpName (_ : Typed.name tags_t) => unimplemented
    | ExpArrayAccess (array : Expression) (index : Expression) => unimplemented
    | ExpBitStringAccess (bits : Expression) (lo : N) (hi : N) => unimplemented
    | ExpList (value : list Expression) => unimplemented
    | ExpRecord (entries : list KeyValue) => unimplemented
    | ExpUnaryOp (op : OpUni) (arg : Expression) => unimplemented
    | ExpBinaryOp (op : OpBin) (args : (Expression * Expression)) => unimplemented
    | ExpCast (typ : P4Type tags_t) (expr : Expression) => unimplemented
    | ExpTypeMember (typ : Typed.name tags_t) (name : P4String) => unimplemented
    | ExpErrorMember (_ : P4String) => unimplemented
    | ExpExpressionMember (expr : Expression) (name : P4String) => unimplemented
    | ExpTernary (cond : Expression) (tru : Expression) (fls : Expression) => unimplemented
    | ExpFunctionCall (func : Expression) (type_args : list (P4Type tags_t))
                      (args : list (option Expression)) => unimplemented
    | ExpNamelessInstantiation (typ : P4Type tags_t) (args : list Expression) =>
        _ <- add_decl (instantiate env typ);; args
    | ExpDontCare => unimplemented
    | ExpMask (expr : Expression) (mask : Expression) => unimplemented
    | ExpRange (lo : Expression) (hi : Expression) => unimplemented
    end
  end.

Definition find_instantiation (ds : list (P4light.AST.TopDecl.d + instantiation_expression))
    : option (list (P4light.AST.TopDecl.d + instantiation_expression) * instantiation_expression * list (P4light.AST.TopDecl.d + instantiation_expression))
  := None. (* TODO *)

Fixpoint step (fuel : nat) : (@state_monad state exception unit) :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      fun (ds, _) =>
        match find_instantiation ds with
        | Some (ds1, inst, ds2) =>
            _ <- upd_decl_list nil;;
            _ <- instantiate inst;;
            ds <- get_decl_list;;
            _ <- set_decl_list (ds1 ++ ds ++ ds2);;
            step fuel'
        | None => ret tt
        end
  end.

Fixpoint calc_fuel (prog : Syntax.program) : nat. *)

End P4lightGen.
