Require Import Coq.Strings.String.
Require Import Poulet4.P4flat.Syntax.
Require Import Poulet4.P4flat.GCL.
Require Import Poulet4.Monads.Result.
Import ResultNotations.
Import Dijkstra.

Open Scope string_scope.

Definition var := string.

Inductive p4sorts :=
| Bool
| Bit (width: N)
| Prod (s1 s2 : p4sorts)
| ActionName.

Inductive p4funs :=
| BTrue
| BFalse
| BBitLit (width: N) (val: Z)
(* imprecise but workable *)
| BTable (name: string)
| BProj1
| BProj2
(* Better for this to be an enum or at least an integer *)
| BAction (name: string).


Inductive p4rels :=
(* no relation symbols *)
.

Definition p4sig : Sig.signature :=
  {| Sig.sig_sorts := p4sorts;
     Sig.sig_funs := p4funs;
     Sig.sig_rels := p4rels |}.

Definition mk_action (name: string) : Spec.tm var p4sig :=
  @Spec.TFun _ p4sig (BAction name) [].

Definition lhs_to_var (e: Expr.e) : result string var :=
  match e with
  | Expr.Var _ s _ => ok s
  | _ => error "lvals besides vars not implemented"
  end.

Definition e_to_tm (e: Expr.e) : result string (Spec.tm var p4sig) :=
  match e with
  | Expr.Bit width val =>
      ok (@Spec.TFun _ p4sig (BBitLit width val) [])
  | Expr.Var _ name _ =>
      ok (@Spec.TVar _ _ name)
  | _ => error "e_to_tm unimplemented"
  end.

Fixpoint s_to_stmt (s: Stmt.s) : result string (stmt var p4sig) :=
  match s with
  | Stmt.Skip => ok (GSkip _ _)
  | Stmt.Return e => error "return unimplemented"
  | Stmt.Exit => error "exit unimplemented"
  | Stmt.Assign lhs rhs =>
      let* lhs' := lhs_to_var lhs in
      let* rhs' := e_to_tm rhs in
      ok (GAssign lhs' rhs')
  | Stmt.ExternCall extern_instance_name method_name type_args args returns =>
      error "extern call unimplemented"
  | Stmt.Table ctrl_plane_name key actions =>
      let* key' := sequence (List.map e_to_tm key) in
      (* XXX generate an actually fresh variable here *)
      let result_var := ctrl_plane_name ++ "__res" in
      let call_tm := @Spec.TFun var p4sig (BTable ctrl_plane_name) key' in
      let call_stmt := GAssign result_var call_tm in
      let act_choice := @Spec.TFun var p4sig BProj1 [Spec.TVar result_var] in
      let* actions_stmts :=
        sequence (List.map (fun '(name, stmt) =>
                              let+ stmt' := s_to_stmt stmt in  
                              GSeq (GAssume (Spec.FEq act_choice (mk_action name)))
                                   stmt')
                           actions) in
      let actions_stmt := List.fold_right GChoice (GSkip _ _) actions_stmts in
      ok (GSeq call_stmt actions_stmt)
  | Stmt.Var original_name (inl typ) tail =>
      (* declaration is a no-op. *)
      s_to_stmt tail
  | Stmt.Var original_name (inr rhs) tail =>
      let* rhs' := e_to_tm rhs in
      let* tail' := s_to_stmt tail in
      ok (GSeq (GAssign original_name rhs') tail')
  | Stmt.Seq head tail =>
      let* head' := s_to_stmt head in
      let* tail' := s_to_stmt tail in
      ok (GSeq head' tail')
  | Stmt.Conditional guard tru_blk fls_blk =>
      let* guard' := e_to_tm guard in
      let then_cond := Spec.FEq guard' (@Spec.TFun var p4sig BTrue []) in
      let else_cond := Spec.FNeg then_cond in
      let* tru_blk' := s_to_stmt tru_blk in
      let* fls_blk' := s_to_stmt fls_blk in
      ok (GChoice (GSeq (GAssume then_cond) tru_blk')
                  (GSeq (GAssume else_cond) fls_blk'))
  end.

Definition prog_to_stmt (p: TopDecl.prog) :=
  let* (_, main_args) := TopDecl.find_decl "main" p
                         >>= TopDecl.expect_pkg in
  let* ctrl := match main_args with
               | [ctrl] => ok ctrl
               | _ => error "wrong number of args to main pkg (expected exactly 1)"
               end in
  let* (_, cparams, cstmt) := TopDecl.find_decl ctrl p
                              >>= TopDecl.expect_controlblock in
  s_to_stmt cstmt.
