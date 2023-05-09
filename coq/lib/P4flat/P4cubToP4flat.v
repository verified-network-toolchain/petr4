From Coq Require Import
     Strings.String
     Lists.List.
Require Import Poulet4.Monads.Result.
Require Poulet4.P4cub.Syntax.Syntax.
Require Poulet4.P4flat.Syntax.

Import ResultNotations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* C for cub *)
Module C := P4cub.Syntax.AST.
Check C.Exp.t.

(* F for flat *)
Module F := P4flat.Syntax.
Check F.Exp.t.

(* Functions and actions. *)
Record func_template: Type :=
  {ft_body: F.Stm.t}.

(* Controls and parsers. *)
Record instance_template: Type :=
  {inst_body: F.Stm.t}.

Record flatten_env : Type :=
  MkFlattenEnv { fe_funcs: Envn.Env.t string func_template;
                 fe_instances: Envn.Env.t string instance_template;
                 fe_tables: Envn.Env.t string F.Stm.t; }.

Definition empty_env : flatten_env :=
  MkFlattenEnv (Envn.Env.empty _ _)
               (Envn.Env.empty _ _)
               (Envn.Env.empty _ _).

Definition find_func
           (fenv: flatten_env)
           (f: C.Call.t)
  : result string func_template :=
  error "sorry".

Definition find_instance
           (fenv: flatten_env)
           (name: string)
  : result string instance_template :=
  error "sorry".

Definition specialize_func
           (ft: func_template)
           (args: C.Exp.args)
  : result string F.Stm.t :=
  error "sorry".

Definition specialize_instance
           (inst: instance_template)
           (extern_args: list string)
           (args: C.Exp.args)
  : result string F.Stm.t :=
  error "sorry".

Definition find_table
           (fenv: flatten_env)
           (table_name: string)
  : result string F.Stm.t :=
  error "sorry".

Definition add_control
           (control: C.Top.t)
           (fenv: flatten_env) : flatten_env :=
  fenv.

Definition add_parser
           (parser: C.Top.t)
           (fenv: flatten_env) : flatten_env :=
  fenv.

Definition add_function
           (function_name : string)
           (type_params : nat)
           (signature : C.Typ.arrowT)
           (body : F.Stm.t)
  : flatten_env -> flatten_env :=
  fun fe => fe.

(* doesn't have to do anything but included for later adjustment *)
Definition translate_expr (e : C.Exp.t) : result string F.Exp.t :=
  ok e.

Fixpoint translate_stmt (fenv: flatten_env) (s : C.Stm.t) : result string F.Stm.t :=
  match s with
  | C.Stm.Skip => ok F.Stm.Skip
  | C.Stm.SetValidity _ _ =>
      error "failed while translating .setValid"
  | C.Stm.Ret e =>
      (* It would be better to solve this problem at the P4cub level
      by adopting an RTL-like setup where returns are always in tail
      position. Then we don't have to deal with early returns in the
      inliner. *)
      error "Failed while translating return statement. Returns are not currently supported in the P4flat inliner."
  | C.Stm.Exit =>
      (* Similar problems to return, but with additional bookkeeping
      required for bubbling the exit up. I'm okay with doing that work
      here and not in P4cub, but it should at least make sure the
      exits are in tail position. *)
      error "Failed while translating exit statement. Exits are not currently supported in the P4flat inliner."
  | C.Stm.Trans trns =>
      error "Failed while translating transition statement. Parsers are not currently supported in the P4flat inliner."
  | C.Stm.Asgn lhs rhs =>
      let* lhs' := translate_expr lhs in
      let+ rhs' := translate_expr rhs in
      F.Stm.Assign lhs' rhs'
  | C.Stm.App (C.Call.Method _ _ _ _) args =>
      error "extern method calls unimplemented"
  | C.Stm.App (C.Call.Inst instance_name ext_args) args =>
      let* block := find_instance fenv instance_name in
      specialize_instance block ext_args args
  | C.Stm.App call args =>
      let* func_body := find_func fenv call in
      specialize_func func_body args
  | C.Stm.Invoke lhs table_name =>
      find_table fenv table_name
  | C.Stm.LetIn original_name (inl typ) tail =>
      error "uninitialized variables not currently supported"
  | C.Stm.LetIn original_name (inr expr) tail =>
      let* expr' := translate_expr expr in
      let+ tail' := translate_stmt fenv tail in
      F.Stm.Var original_name (inr expr') tail'
  | C.Stm.Seq head tail =>
      let* head' := translate_stmt fenv head in
      let+ tail' := translate_stmt fenv tail in
      F.Stm.Seq head' tail'
  | C.Stm.Cond guard tru_blk fls_blk =>
      let* guard' := translate_expr guard in
      let* tru_blk' := translate_stmt fenv tru_blk in
      let+ fls_blk' := translate_stmt fenv fls_blk in
      F.Stm.Conditional guard' tru_blk' fls_blk'
  end.

Definition translate_decl (fenv: flatten_env) (decl: C.Top.t) : result string (flatten_env * list F.Top.t) :=
  match decl with
  | C.Top.Instantiate constructor_name instance_name type_args cargs expr_cargs =>
      error "todo: hard part"
  | C.Top.Extern extern_name type_params cparams expr_cparams methods =>
      ok (fenv, [F.Top.Extern extern_name type_params cparams expr_cparams methods])
  | C.Top.Control _ _ _ _ _ _ _ =>
      ok (add_control decl fenv, [])
  | C.Top.Parser _ _ _ _ _ _ _ =>
      ok (add_parser decl fenv, [])
  | C.Top.Funct function_name type_params signature body =>
      let+ body' := translate_stmt fenv body in
      (add_function function_name type_params signature body' fenv, [])
  end.

Fixpoint translate_decls (fenv: flatten_env) (p: list C.Top.t)
  : result string (list F.Top.t) :=
  match p with
  | decl :: decls =>
      let* (fenv, flat_decl) := translate_decl fenv decl in
      let* flat_decls := translate_decls fenv decls in
      ok (flat_decl ++ flat_decls)
  | [] => ok []
  end.

Definition translate_prog (p: C.Top.prog) : result string F.Top.prog :=
  translate_decls empty_env p.
