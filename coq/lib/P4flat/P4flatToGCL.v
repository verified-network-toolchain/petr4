Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4flat.Syntax.
Require Import Poulet4.P4flat.GGCL.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.ExceptionState.
Require Import Poulet4.Utils.Envn.
Require Poulet4.Utils.NameGen.
Require stdpp.gmap.
Print gmap.gmap.
Import ResultNotations.
Import Dijkstra.

Module GEN := NameGen.NameGenParam.
Open Scope string_scope.

Definition var := string.

Record tbl_sig :=
  { tbl_sig_key: AST.Typ.t;
    tbl_sig_acts: list (string * Exp.args * Stm.t) }.

(* A map from table names to table signatures. *)
Definition tbl_map :=
  Env.t string tbl_sig.

(* A map from de Bruijn indices to fresh names. *)
Definition idx_map := list string.
Definition idx_map_init : idx_map := [].
Definition var_env := GEN.t AST.Typ.t.
Definition var_env_init : var_env := GEN.init.

Notation M := (state_monad var_env string).

Definition freshen_name (s: string) (t: AST.Typ.t) : M string :=
  let* e := get_state in
  let (s, e') := GEN.freshen e s t in
  put_state e';;
  mret s.

Definition declare_var (name: string) (typ: AST.Typ.t) (m: idx_map) : M idx_map :=
  let* name' := freshen_name name typ in
  mret (name' :: m).

Definition declare_param (name: string) (param: CUB.Typ.param) : idx_map -> M idx_map :=
  let typ := match param with
             | PAIn t
             | PAOut t 
             | PAInOut t => t
             end
  in
  declare_var name typ.
    
Definition declare_params (params: CUB.Typ.params) : idx_map -> M idx_map :=
  fold_left_monad (fun m '(name, p) => declare_param name p m) params.

Definition find_var (m: idx_map) (k: nat) : M string :=
  from_opt (nth_error m k) "find_var: index not found in idx_map".

Inductive p4sorts :=
| Bool
| Bit (width: N)
| Prod (s1 s2 : p4sorts)
| ActionName.
Scheme Equality for p4sorts.
#[global]
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
| BAction (name: string)
| BVar (name: string).
Scheme Equality for p4funs.
#[global]
Instance p4funs_EqDec : EqDec p4funs eq := 
  p4funs_eq_dec.

Inductive p4rels :=
(* no relation symbols *)
.
Scheme Equality for p4rels.
#[global]
Instance p4rels_EqDec : EqDec p4rels eq := 
  p4rels_eq_dec.

Definition p4sig :=
  Sig.signature p4sorts p4funs p4rels.

Definition initial_p4sig : p4sig :=
  {| Sig.sig_sorts :=
    fun s =>
      match s with
      | Bool => Some 0
      | ActionName => Some 0
      | _ => None
      end;
    Sig.sig_funs := fun f =>
                        if f == Sig.SSimple BTrue
                        then Some ([], (Sig.SSimple Bool))
                        else if f == Sig.SSimple BFalse
                             then Some ([], (Sig.SSimple Bool))
                             else None;
     Sig.sig_rels := fun _ => None |}.

Definition mk_action (name: string) : Spec.tm var p4funs :=
  Spec.TFun (Sig.SSimple (BAction name)) [].

Definition lhs_to_var (m: idx_map) (e: Exp.t) : M var :=
  match e with
  | Exp.Var _ _ idx => find_var m idx
  | _ => error "lvals other than vars are not yet implemented"
  end.

Definition e_to_tm (e: Exp.t) : M (Spec.tm var p4funs) :=
  match e with
  | Exp.Bit width val => mret (Spec.TFun (Sig.SSimple (BBitLit width val)) [])
  | Exp.Var _ name _ => mret (Spec.TVar name)
  | _ => error "e_to_tm unimplemented"
  end.

Fixpoint s_to_stmt (m: idx_map) (s: Stm.t) : M (stmt var p4funs p4rels) :=
  match s with
  | Stm.Skip => mret (GSkip _ _ _)
  | Stm.Ret e => (error "return unimplemented")
  | Stm.Exit => (error "exit unimplemented")
  | Stm.Asgn lhs rhs =>
      let* lhs' := lhs_to_var m lhs in
      let* rhs' := e_to_tm rhs in
      mret (GAssign lhs' rhs')
  | Stm.AppMethod extern_instance_name method_name type_args args returns =>
      (error "extern call unimplemented")
  | Stm.Invoke lhs ctrl_plane_name key actions =>
      let* key' := sequence (List.map e_to_tm key) in
      (* XXX generate an actually fresh variable here *)
      let result_var := ctrl_plane_name ++ "__res" in
      let call_tm := Spec.TFun (Sig.SSimple (BTable ctrl_plane_name)) key' in
      let call_stmt := GAssign result_var call_tm in
      let act_choice := Spec.TFun (Sig.SSimple BProj1) [Spec.TVar result_var] in
      let* actions_stmts :=
        sequence (List.map (fun '(name, params, stmt) =>
                              let* stmt' := s_to_stmt m stmt in  
                              mret (GSeq (GAssume (Spec.FEq act_choice (mk_action name)))
                                         stmt'))
                           actions) in
      let actions_stmt := List.fold_right GChoice (GSkip _ _ _) actions_stmts in
      mret (GSeq call_stmt actions_stmt)
  | Stm.LetIn original_name (inl typ) tail =>
      let* m' := declare_var original_name typ m in
      s_to_stmt m' tail
  | Stm.LetIn original_name (inr rhs) tail =>
      let* rhs' := e_to_tm rhs in
      let* m := declare_var original_name (typ_of_exp rhs) m in
      let* tail' := s_to_stmt m tail in
      mret (GSeq (GAssign original_name rhs') tail')
  | Stm.Seq head tail =>
      let* head' := s_to_stmt m head in
      let* tail' := s_to_stmt m tail in
      mret (GSeq head' tail')
  | Stm.Cond guard tru_blk fls_blk =>
      let* guard' := (e_to_tm guard) in
      let then_cond := Spec.FEq guard' (Spec.TFun (Sig.SSimple BTrue) []) in
      let else_cond := Spec.FNeg then_cond in
      let* tru_blk' := s_to_stmt m tru_blk in
      let* fls_blk' := s_to_stmt m fls_blk in
      mret (GChoice (GSeq (GAssume then_cond) tru_blk')
                       (GSeq (GAssume else_cond) fls_blk'))
  | Stm.SetValidity _ _ =>
      (error "SetValidity unimplemented")
  end.

Definition typ_to_sort (t: Typ.t) : option p4sorts :=
  match t with
  | Typ.Bool => mret Bool
  | Typ.VarBit k => mret (Bit k)
  | Typ.Bit k => mret (Bit k)
  | Typ.Int p => mret (Bit (Npos p))
  | Typ.Error => None
  | Typ.Array _ _ => None
  | Typ.Struct _ _ => None
  | Typ.Var k => None
  end.

Definition typed_var_to_ranked_sym (typed_var: string * Typ.t) : option (p4funs * (Sig.rank p4sorts * Sig.sort p4sorts)) :=
  let (var, type) := typed_var in
  let* ret := typ_to_sort type in
  mret (BVar var, ([], Sig.SSimple ret)).

Definition var_env_to_fsig (env: var_env) : option (Sig.fsignature p4sorts p4funs p4rels) :=
  let bindings : list (string * Typ.t) := gmap.gmap_to_list env in
  let* funs := sequence (map typed_var_to_ranked_sym bindings) in
  mret {| Sig.fsig_sorts := [];
          Sig.fsig_funs := funs;
          Sig.fsig_rels := [] |}.

Definition prog_to_sig_stmt (p: Top.prog) : M (Sig.fsignature p4sorts p4funs p4rels *
                                               stmt var p4funs p4rels) :=
  let* (_, main_args) := from_result (Top.find_decl "main" p
                                      >>= Top.expect_pkg) in
  let* ctrl := match main_args with
               | [ctrl] => mret ctrl
               | _ => error "wrong number of args to main pkg (expected exactly 1)"
               end in
  let* (_, eparams, params, cstmt) := from_result (Top.find_decl ctrl p
                                                   >>= Top.expect_controlblock) in
  let* m := declare_params params idx_map_init in 
  let* res := s_to_stmt m cstmt in
  let* env := get_state in
  let* fsig := ExceptionState.from_opt (var_env_to_fsig env)
                                       "conversion to fsig failed" in
  mret (fsig, res).
