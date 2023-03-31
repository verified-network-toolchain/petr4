Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Poulet4.P4flat.Syntax.
Require Import Poulet4.P4flat.GGCL.
Require Import Poulet4.Monads.Result.
Require Import Poulet4.Monads.State.
Import ResultNotations.
Import Dijkstra.

Open Scope string_scope.

Definition var := string.

Inductive p4sorts :=
| Bool
| Bit (width: N)
| Prod (s1 s2 : p4sorts)
| ActionName.
Scheme Equality for p4sorts.
Instance p4sorts_EqDec : EqDec p4sorts eq := 
  p4sorts_eq_dec.

Inductive p4funs :=
| BTrue
| BFalse
| BBitLit (width: N) (val: Z)
| BTable (name: string)
| BProj1
| BProj2
(* Better for this to be an enum or at least an integer *)
| BAction (name: string).
Scheme Equality for p4funs.
Instance p4funs_EqDec : EqDec p4funs eq := 
  p4funs_eq_dec.

Inductive p4rels :=
(* no relation symbols *)
.
Scheme Equality for p4rels.
Instance p4rels_EqDec : EqDec p4rels eq := 
  p4rels_eq_dec.

Definition p4sig :=
  Sig.signature p4sorts p4funs p4rels.

Definition initial_p4sig : p4sig :=
  {| Sig.sig_sorts := [ (Bool, 0); (ActionName, 0) ];
    Sig.sig_funs := fun f =>
                        if f == Sig.SSimple BTrue
                        then Some ([], (Sig.SSimple Bool))
                        else if f == Sig.SSimple BFalse
                             then Some ([], (Sig.SSimple Bool))
                             else None;
     Sig.sig_rels := fun _ => None |}.

Definition mk_action (name: string) : Spec.tm var p4funs :=
  Spec.TFun (Sig.SSimple (BAction name)) [].

Definition lhs_to_var (e: Expr.e) : result string var :=
  match e with
  | Expr.Var _ s _ => ok s
  | _ => error "lvals besides vars not implemented"
  end.

Definition e_to_tm (e: Expr.e) : result string (Spec.tm var p4funs) :=
  match e with
  | Expr.Bit width val => ok (Spec.TFun (Sig.SSimple (BBitLit width val)) [])
  | Expr.Var _ name _ => ok (Spec.TVar name)
  | _ => error "e_to_tm unimplemented"
  end.

Fixpoint s_to_stmt (s: Stmt.s) : StateT p4sig (result string) (stmt var p4funs p4rels) :=
  match s with
  | Stmt.Skip => mret (GSkip _ _ _)
  | Stmt.Return e => state_lift (error "return unimplemented")
  | Stmt.Exit => state_lift (error "exit unimplemented")
  | Stmt.Assign lhs rhs =>
      let* lhs' := state_lift (lhs_to_var lhs) in
      let* rhs' := state_lift (e_to_tm rhs) in
      mret (GAssign lhs' rhs')
  | Stmt.ExternCall extern_instance_name method_name type_args args returns =>
      state_lift (error "extern call unimplemented")
  | Stmt.Table ctrl_plane_name key actions =>
      let* key' := state_lift (sequence (List.map e_to_tm key)) in
      (* XXX generate an actually fresh variable here *)
      let result_var := ctrl_plane_name ++ "__res" in
      let call_tm := Spec.TFun (Sig.SSimple (BTable ctrl_plane_name)) key' in
      let call_stmt := GAssign result_var call_tm in
      let act_choice := Spec.TFun (Sig.SSimple BProj1) [Spec.TVar result_var] in
      let* actions_stmts :=
        sequence (List.map (fun '(name, params, stmt) =>
                              let* stmt' := s_to_stmt stmt in  
                              mret (GSeq (GAssume (Spec.FEq act_choice (mk_action name)))
                                         stmt'))
                           actions) in
      let actions_stmt := List.fold_right GChoice (GSkip _ _ _) actions_stmts in
      mret (GSeq call_stmt actions_stmt)
  | Stmt.Var original_name (inl typ) tail =>
      (* declaration is a no-op. *)
      s_to_stmt tail
  | Stmt.Var original_name (inr rhs) tail =>
      let* rhs' := state_lift (e_to_tm rhs) in
      let* tail' := s_to_stmt tail in
      mret (GSeq (GAssign original_name rhs') tail')
  | Stmt.Seq head tail =>
      let* head' := s_to_stmt head in
      let* tail' := s_to_stmt tail in
      mret (GSeq head' tail')
  | Stmt.Conditional guard tru_blk fls_blk =>
      let* guard' := state_lift (e_to_tm guard) in
      let then_cond := Spec.FEq guard' (Spec.TFun (Sig.SSimple BTrue) []) in
      let else_cond := Spec.FNeg then_cond in
      let* tru_blk' := s_to_stmt tru_blk in
      let* fls_blk' := s_to_stmt fls_blk in
      mret (GChoice (GSeq (GAssume then_cond) tru_blk')
                    (GSeq (GAssume else_cond) fls_blk'))
  end.

Definition prog_to_stmt (p: TopDecl.prog) : StateT p4sig
                                                   (result string)
                                                   (stmt var p4funs p4rels) :=
  let* (_, main_args) := state_lift (TopDecl.find_decl "main" p
                                     >>= TopDecl.expect_pkg) in
  let* ctrl := match main_args with
               | [ctrl] => mret ctrl
               | _ => state_lift (error "wrong number of args to main pkg (expected exactly 1)")
               end in
  let* (_, cparams, cstmt) := state_lift (TopDecl.find_decl ctrl p
                                          >>= TopDecl.expect_controlblock) in
  s_to_stmt cstmt.
