Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4flat.Syntax.
Require Import Poulet4.P4flat.GGCL.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.ExceptionState.
Require Import Poulet4.Utils.Envn.
Require Import Poulet4.Utils.AList.
Require Poulet4.Utils.NameGen.
Require stdpp.list.
Require stdpp.gmap.
Print gmap.gmap.
Import ResultNotations.

Module GEN := NameGen.NameGenParam.
Open Scope string_scope.

(* A map from de Bruijn indices to fresh names. *)
Definition idx_map := list string.
Definition idx_map_init : idx_map := [].
Inductive vartyp :=
| LocalVar (typ: AST.Typ.t)
| TableFun (key_typ: list Typ.t) (act_arg_typs: list Typ.t).
Definition var_env := GEN.t vartyp.
Definition var_env_init : var_env := GEN.init.

Notation M := (state_monad var_env string).

Definition freshen_vartyp (s: string) (t: vartyp) : M string :=
  let* e := get_state in
  let (s, e') := GEN.freshen e s t in
  put_state e';;
  mret s.

Definition freshen_name (s: string) (t: AST.Typ.t) : M string :=
  freshen_vartyp s (LocalVar t).

Definition freshen_tbl_name
           (s: string)
           (key_typ: list Typ.t)
           (act_arg_typs: list Typ.t) : M string :=
  freshen_vartyp s (TableFun key_typ act_arg_typs).

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
| Prod (s1 s2 : p4sorts).
Scheme Equality for p4sorts.
#[global]
Instance p4sorts_EqDec : EqDec p4sorts eq := 
  p4sorts_eq_dec.

(* Function symbols common to all P4 programs. *)
Inductive p4funs_base :=
| BTrue
| BFalse
| BBitLit (width: N) (val: Z)
| BProj1
| BProj2.
Scheme Equality for p4funs_base.
#[global]
Instance p4funs_base_EqDec : EqDec p4funs_base eq :=
  p4funs_base_eq_dec.

(* Function symbols arising from particular programs. *)
Inductive p4funs_prog :=
| BTable (name: string)
| BAction (name: string).
Scheme Equality for p4funs_prog.
#[global]
Instance p4funs_prog_EqDec : EqDec p4funs_prog eq :=
  p4funs_prog_eq_dec.

Definition p4funs : Type :=
  p4funs_base + p4funs_prog.
#[global]
Instance p4funs_EqDec : EqDec p4funs eq :=
  ltac:(typeclasses eauto).

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
      | Bool => true
      | Bit k => true
      | _ => false
      end;
    Sig.sig_funs := fun f =>
                      if Sig.ident_EqDec f (Sig.SSimple (inl BTrue))
                      then Some ([], (Sig.SSimple Bool))
                      else if f == Sig.SSimple (inl BFalse)
                           then Some ([], (Sig.SSimple Bool))
                           else None;
    Sig.sig_rels := fun _ => None |}.
  
Definition mk_action (actions: list (string * Exp.args * Stm.t)) (name: string) : Spec.tm string p4funs :=
  let act_names := List.map (fun '(name, args, stm) => name) actions in
  match ListUtil.index_of strings.string_eq_dec name act_names with
  | Some idx_nat =>
      let idx_z := BinInt.Z.of_nat idx_nat in
      Spec.TFun (Sig.SSimple (inl (BBitLit 8%N idx_z))) []
  | None =>
      Spec.TFun (Sig.SSimple (inl (BBitLit 8%N BinInt.Z.zero))) []
  end.

Definition lhs_to_var (m: idx_map) (e: Exp.t) : M string :=
  match e with
  | Exp.Var _ _ idx => find_var m idx
  | _ => error "lvals other than vars are not yet implemented"
  end.

Definition e_to_tm (e: Exp.t) : M (Spec.tm string p4funs) :=
  match e with
  | Exp.Bit width val => mret (Spec.TFun (Sig.SSimple (inl (BBitLit width val))) [])
  | Exp.Var _ name _ => mret (Spec.TVar name)
  | _ => error "e_to_tm unimplemented"
  end.

Fixpoint s_to_stmt (m: idx_map) (s: Stm.t)
  : M (stmt string p4funs p4rels) :=
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
      let keytyps := List.map typ_of_exp key in
      (* XXX generate an actually fresh variable here *)
      let result_var := ctrl_plane_name ++ "__res" in
      let call_tm := Spec.TFun (Sig.SSimple (inr (BTable ctrl_plane_name))) key' in
      let call_stmt := GAssign result_var call_tm in
      let act_choice := Spec.TFun (Sig.SSimple (inl BProj1)) [Spec.TVar result_var] in
      let* actions_stmts :=
        sequence (List.map (fun '(name, params, stmt) =>
                              let* stmt' := s_to_stmt m stmt in  
                              mret (GSeq (GAssume (Spec.FEq act_choice (mk_action actions name)))
                                         stmt'))
                           actions) in
      let actions_stmt := List.fold_right GChoice (GSkip _ _ _) actions_stmts in
      freshen_tbl_name ctrl_plane_name keytyps [Typ.Bit 1; Typ.Bit 1];;
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
      let then_cond := Spec.FEq guard' (Spec.TFun (Sig.SSimple (inl BTrue)) []) in
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

Definition nonempty_list_to_prod (l: list p4sorts) : option p4sorts :=
  match l with
  | x :: l' =>
      Some (List.fold_left Prod l' x)
  | [] =>
      None
  end.

Definition vartyp_to_var_or_sym (typed_var: string * vartyp)
  : option (string * Sig.sort p4sorts + p4funs_prog * (Sig.rank p4sorts * Sig.sort p4sorts)) :=
  let (var, vt) := typed_var in
  match vt with
  | LocalVar type =>
      let* sort := typ_to_sort type in
      mret (inl (var, Sig.SSimple sort))
  | TableFun key_typs act_arg_typs =>
      let* args := sequence (List.map typ_to_sort key_typs) in
      let* rets := sequence (List.map typ_to_sort act_arg_typs) in
      let* ret := nonempty_list_to_prod rets in
      mret (inr (BTable var, (List.map Sig.SSimple args, Sig.SSimple ret)))
  end.

Definition vartyps_to_vars_syms
           (bindings: list (string * vartyp))
  : option (list (string * Sig.sort p4sorts) *
           (list (p4funs_prog * (Sig.rank p4sorts * Sig.sort p4sorts)))) :=
  let* vars_or_syms := sequence (map vartyp_to_var_or_sym bindings) in
  Some (base.omap option.maybe_inl vars_or_syms,
        base.omap option.maybe_inr vars_or_syms).

Definition var_env_to_vars_funs (env: var_env) : option (AList string (Sig.sort p4sorts) eq *
                                                         AList p4funs_prog (Sig.rank p4sorts * Sig.sort p4sorts) eq) :=
  let bindings : list (string * vartyp) := gmap.gmap_to_list env in
  vartyps_to_vars_syms bindings.

Definition prog_to_sig_stmt (p: Top.prog)
  : M (AList p4funs_prog (Sig.rank p4sorts * Sig.sort p4sorts) eq *
       list (string * Sig.sort p4sorts) *
       stmt string p4funs p4rels) :=
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
  let* (vars, fsig) :=
    ExceptionState.from_opt (var_env_to_vars_funs env)
                            "conversion to fsig failed" in
  mret (fsig, vars, res).
