open AST0
open AST
open Auxilary
open BinIntDef
open BinNums
open BinPos
open CCompEnv
open Clight
open Cop
open Ctypes
open Datatypes
open Envn
open EquivDec
open EquivUtil
open Errors
open Helloworld
open Integers
open List0

module P = P4cub
module Coq__1 = P

module F = P.F

module E = P.Expr

module ST = P.Stmt

module PA = P.Parser

module CT = P.Control

module TD = P.TopDecl

(** val print_Clight : Clight.program -> unit **)

let print_Clight = CompCert.Cfrontend.PrintClight.print_if

type identMap = (char list, ident) Env.t

(** val coq_CTranslateType :
    E.t -> coq_ClightEnv -> coq_type * coq_ClightEnv **)

let rec coq_CTranslateType p4t env =
  match p4t with
  | E.TBool -> (type_bool, env)
  | E.TBit _ -> ((Tlong (Unsigned, noattr)), env)
  | E.TInt _ -> ((Tlong (Signed, noattr)), env)
  | E.TStruct fields ->
    (match lookup_composite env p4t with
     | Some comp -> ((Tstruct ((name_composite_def comp), noattr)), env)
     | None ->
       let (env_top_id, top_id) = new_ident env in
       let (members, env_fields_declared) =
         F.fold (fun _ field cumulator ->
           let (members_prev, env_prev) = cumulator in
           let (new_t, new_env) = coq_CTranslateType field env_prev in
           let (new_env0, new_id) = new_ident new_env in
           (((new_id, new_t) :: members_prev), new_env0)) fields ([],
           env_top_id)
       in
       let comp_def = Composite (top_id, Struct, members, noattr) in
       let env_comp_added = add_composite_typ env_fields_declared p4t comp_def
       in
       ((Tstruct (top_id, noattr)), env_comp_added))
  | E.THeader fields ->
    (match lookup_composite env p4t with
     | Some comp -> ((Tstruct ((name_composite_def comp), noattr)), env)
     | None ->
       let (env_top_id, top_id) = new_ident env in
       let (members, env_fields_declared) =
         F.fold (fun _ field cumulator ->
           let (members_prev, env_prev) = cumulator in
           let (new_t, new_env) = coq_CTranslateType field env_prev in
           let (new_env0, new_id) = new_ident new_env in
           (((new_id, new_t) :: members_prev), new_env0)) fields ([],
           env_top_id)
       in
       let comp_def = Composite (top_id, Struct, members, noattr) in
       let env_comp_added = add_composite_typ env_fields_declared p4t comp_def
       in
       ((Tstruct (top_id, noattr)), env_comp_added))
  | _ -> (Tvoid, env)

(** val coq_CTranslateSlice :
    expr -> positive -> positive -> E.t -> coq_ClightEnv ->
    (expr * coq_ClightEnv) option **)

let coq_CTranslateSlice x hi lo _ env =
  let hi' = Econst_int ((Int.repr (Zpos hi)), (Tint (I32, Unsigned, noattr)))
  in
  let lo' = Econst_int ((Int.repr (Zpos lo)), (Tint (I32, Unsigned, noattr)))
  in
  let one' = Econst_long (Int64.one, (Tlong (Unsigned, noattr))) in
  Some ((Ebinop (Oand, (Ebinop (Oshr, x, lo', (Tlong (Unsigned, noattr)))),
  (Ebinop (Osub, (Ebinop (Oshl, one', (Ebinop (Oadd, one', (Ebinop (Osub,
  hi', lo', (Tlong (Unsigned, noattr)))), (Tlong (Unsigned, noattr)))),
  (Tlong (Unsigned, noattr)))), one', (Tlong (Unsigned, noattr)))), (Tlong
  (Unsigned, noattr)))), env)

(** val coq_CTranslateExpr :
    'a1 E.e -> coq_ClightEnv -> (expr * coq_ClightEnv) option **)

let rec coq_CTranslateExpr e0 env =
  match e0 with
  | E.EBool (b, _) ->
    if b
    then Some ((Econst_int (Int.one, type_bool)), env)
    else Some ((Econst_int (Int.zero, type_bool)), env)
  | E.EBit (w, n, _) ->
    if Pos.leb w
         (Pos.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    then Some ((Econst_long ((Int64.repr n), (Tlong (Unsigned, noattr)))),
           env)
    else None
  | E.EInt (w, n, _) ->
    if Pos.leb w
         (Pos.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    then Some ((Econst_long ((Int64.repr n), (Tlong (Signed, noattr)))), env)
    else None
  | E.EVar (ty, x, _) ->
    let (cty, env_ty) = coq_CTranslateType ty env in
    (match find_ident_temp_arg env_ty x with
     | Some p ->
       let (_, tempid) = p in Some ((Etempvar (tempid, cty)), env_ty)
     | None ->
       (match find_ident env_ty x with
        | Some id -> Some ((Evar (id, cty)), env_ty)
        | None ->
          let env' = add_var env_ty x cty in
          (match find_ident env' x with
           | Some id' -> Some ((Evar (id', cty)), env')
           | None -> None)))
  | E.ESlice (n, _UU03c4_, hi, lo, _) ->
    (match coq_CTranslateExpr n env with
     | Some p ->
       let (n', env') = p in coq_CTranslateSlice n' hi lo _UU03c4_ env'
     | None -> None)
  | E.EUop (op, ty, x, _) ->
    let (cty, env_ty) = coq_CTranslateType ty env in
    (match coq_CTranslateExpr x env_ty with
     | Some p ->
       let (x', env') = p in
       (match op with
        | E.Not -> Some ((Eunop (Onotbool, x', cty)), env')
        | E.BitNot -> Some ((Eunop (Onotint, x', cty)), env')
        | E.UMinus -> Some ((Eunop (Oneg, x', cty)), env')
        | _ -> None)
     | None -> None)
  | E.EBop (op, tx, ty, x, y, _) ->
    let (ctx, env_tx) = coq_CTranslateType tx env in
    let (_, env_ty) = coq_CTranslateType ty env_tx in
    (match coq_CTranslateExpr x env_ty with
     | Some p ->
       let (x', env') = p in
       (match coq_CTranslateExpr y env' with
        | Some p0 ->
          let (y', env'') = p0 in
          (match op with
           | E.Plus -> Some ((Ebinop (Oadd, x', y', ctx)), env'')
           | E.PlusSat -> None
           | E.Minus -> Some ((Ebinop (Osub, x', y', ctx)), env'')
           | E.MinusSat -> None
           | E.Times -> Some ((Ebinop (Omul, x', y', ctx)), env'')
           | E.Shl -> Some ((Ebinop (Oshl, x', y', ctx)), env'')
           | E.Shr -> Some ((Ebinop (Oshr, x', y', ctx)), env'')
           | E.Le -> Some ((Ebinop (Ole, x', y', type_bool)), env'')
           | E.Ge -> Some ((Ebinop (Oge, x', y', type_bool)), env'')
           | E.Lt -> Some ((Ebinop (Olt, x', y', type_bool)), env'')
           | E.Gt -> Some ((Ebinop (Ogt, x', y', type_bool)), env'')
           | E.Eq -> Some ((Ebinop (Oeq, x', y', type_bool)), env'')
           | E.NotEq -> Some ((Ebinop (One, x', y', type_bool)), env'')
           | E.BitAnd -> Some ((Ebinop (Oand, x', y', ctx)), env'')
           | E.BitXor -> Some ((Ebinop (Oxor, x', y', ctx)), env'')
           | E.PlusPlus ->
             let shift_amount = Econst_long
               ((Int64.repr (Z.of_nat (SynDefs.width_of_typ ty))), (Tlong
               (Unsigned, noattr)))
             in
             Some ((Ebinop (Oadd, (Ebinop (Oshl, x', shift_amount, ctx)), y',
             ctx)), env'')
           | E.And -> Some ((Ebinop (Oand, x', y', ctx)), env'')
           | _ -> Some ((Ebinop (Oor, x', y', ctx)), env''))
        | None -> None)
     | None -> None)
  | E.EExprMember (y, ty, x, _) ->
    let (_, env_ty) = coq_CTranslateType ty env in
    (match coq_CTranslateExpr x env_ty with
     | Some p ->
       let (x', env') = p in
       (match ty with
        | E.TStruct f0 ->
          (match F.get_index coq_StringEqDec y f0 with
           | Some n ->
             (match F.get coq_StringEqDec y f0 with
              | Some t_member ->
                let (ctm, env_ctm) = coq_CTranslateType t_member env' in
                Some ((Efield (x', (Pos.of_nat n), ctm)), env_ctm)
              | None -> None)
           | None -> None)
        | E.THeader f0 ->
          (match F.get_index coq_StringEqDec y f0 with
           | Some n ->
             (match F.get coq_StringEqDec y f0 with
              | Some t_member ->
                let (ctm, env_ctm) = coq_CTranslateType t_member env' in
                Some ((Efield (x', (Pos.of_nat n), ctm)), env_ctm)
              | None -> None)
           | None -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

(** val coq_CTranslateExprList :
    'a1 E.e list -> coq_ClightEnv -> (expr list * coq_ClightEnv) option **)

let coq_CTranslateExprList el env =
  let transformation = fun a b ->
    match a with
    | Some p ->
      let (el', env') = p in
      (match coq_CTranslateExpr b env' with
       | Some p0 -> let (b', env'') = p0 in Some ((app el' (b' :: [])), env'')
       | None -> None)
    | None -> None
  in
  fold_left transformation el (Some ([], env))

(** val coq_CTranslateDirExprList :
    'a1 E.args -> coq_ClightEnv -> (expr list * coq_ClightEnv) option **)

let coq_CTranslateDirExprList el env =
  let transformation = fun a b ->
    match a with
    | Some p ->
      let (el', env') = p in
      let (_, p0) = b in
      (match p0 with
       | P.PAIn a0 ->
         let (_, e0) = a0 in
         (match coq_CTranslateExpr e0 env' with
          | Some p1 ->
            let (e', env'') = p1 in Some ((app el' (e' :: [])), env'')
          | None -> None)
       | P.PAOut b0 ->
         let (t0, e0) = b0 in
         let (ct0, env_ct) = coq_CTranslateType t0 env' in
         (match coq_CTranslateExpr e0 env_ct with
          | Some p1 ->
            let (e', env'') = p1 in
            let e'0 = Eaddrof (e', (Tpointer (ct0, noattr))) in
            Some ((app el' (e'0 :: [])), env'')
          | None -> None)
       | P.PAInOut b0 ->
         let (t0, e0) = b0 in
         let (ct0, env_ct) = coq_CTranslateType t0 env' in
         (match coq_CTranslateExpr e0 env_ct with
          | Some p1 ->
            let (e', env'') = p1 in
            let e'0 = Eaddrof (e', (Tpointer (ct0, noattr))) in
            Some ((app el' (e'0 :: [])), env'')
          | None -> None))
    | None -> None
  in
  fold_left transformation el (Some ([], env))

(** val coq_CTranslateStatement :
    'a1 ST.s -> coq_ClightEnv -> (statement * coq_ClightEnv) option **)

let rec coq_CTranslateStatement s0 env =
  match s0 with
  | ST.SSkip _ -> Some (Sskip, env)
  | ST.SVardecl (t0, x, _) ->
    let (cty, env_cty) = coq_CTranslateType t0 env in
    Some (Sskip, (add_var env_cty x cty))
  | ST.SAssign (_, e1, e2, _) ->
    (match coq_CTranslateExpr e1 env with
     | Some p ->
       let (e1', env1) = p in
       (match coq_CTranslateExpr e2 env1 with
        | Some p0 -> let (e2', env2) = p0 in Some ((Sassign (e1', e2')), env2)
        | None -> None)
     | None -> None)
  | ST.SConditional (_, e0, s1, s2, _) ->
    (match coq_CTranslateExpr e0 env with
     | Some p ->
       let (e', env1) = p in
       (match coq_CTranslateStatement s1 env1 with
        | Some p0 ->
          let (s1', env2) = p0 in
          (match coq_CTranslateStatement s2 env2 with
           | Some p1 ->
             let (s2', env3) = p1 in Some ((Sifthenelse (e', s1', s2')), env3)
           | None -> None)
        | None -> None)
     | None -> None)
  | ST.SSeq (s1, s2, _) ->
    (match coq_CTranslateStatement s1 env with
     | Some p ->
       let (s1', env1) = p in
       (match coq_CTranslateStatement s2 env1 with
        | Some p0 ->
          let (s2', env2) = p0 in Some ((Ssequence (s1', s2')), env2)
        | None -> None)
     | None -> None)
  | ST.SBlock s1 -> coq_CTranslateStatement s1 env
  | ST.SFunCall (f0, args0, _) ->
    let P.Arrow (args1, returns) = args0 in
    (match returns with
     | Some p ->
       let (t0, e0) = p in
       let (ct0, env_ct) = coq_CTranslateType t0 env in
       (match lookup_function env_ct f0 with
        | Some p0 ->
          let (f', id) = p0 in
          (match coq_CTranslateDirExprList args1 env_ct with
           | Some p1 ->
             let (elist, env') = p1 in
             let (env'0, tempid) = add_temp_nameless env' ct0 in
             (match coq_CTranslateExpr e0 env'0 with
              | Some p2 ->
                let (lvalue, env'1) = p2 in
                Some ((Ssequence ((Scall ((Some tempid), (Evar (id,
                (type_of_function f'))), elist)), (Sassign (lvalue, (Etempvar
                (tempid, ct0)))))), env'1)
              | None -> None)
           | None -> None)
        | None -> None)
     | None ->
       (match lookup_function env f0 with
        | Some p ->
          let (f', id) = p in
          (match coq_CTranslateDirExprList args1 env with
           | Some p0 ->
             let (elist, env') = p0 in
             Some ((Scall (None, (Evar (id, (type_of_function f'))), elist)),
             env')
           | None -> None)
        | None -> None))
  | ST.SActCall (f0, args0, _) ->
    (match lookup_function env f0 with
     | Some p ->
       let (f', id) = p in
       (match coq_CTranslateDirExprList args0 env with
        | Some p0 ->
          let (elist, env') = p0 in
          Some ((Scall (None, (Evar (id, (type_of_function f'))), elist)),
          env')
        | None -> None)
     | None -> None)
  | ST.SReturnVoid _ -> Some ((Sreturn None), env)
  | ST.SReturnFruit (_, e0, _) ->
    (match coq_CTranslateExpr e0 env with
     | Some p -> let (e', env') = p in Some ((Sreturn (Some e')), env')
     | None -> None)
  | _ -> None

(** val coq_CTranslateParserState :
    'a1 PA.state_block -> coq_ClightEnv -> (ident * coq_type) list ->
    (coq_function * coq_ClightEnv) option **)

let coq_CTranslateParserState st env params0 =
  let PA.State (stmt, pe) = st in
  (match coq_CTranslateStatement stmt env with
   | Some p ->
     let (stmt', env') = p in
     (match pe with
      | PA.PGoto (st0, _) ->
        (match st0 with
         | PA.STStart ->
           (match lookup_function env' ('s'::('t'::('a'::('r'::('t'::[]))))) with
            | Some p0 ->
              let (start_f, start_id) = p0 in
              Some ({ fn_return = Tvoid; fn_callconv = { cc_vararg = None;
              cc_unproto = true; cc_structret = true }; fn_params = params0;
              fn_vars = (get_vars env'); fn_temps = (get_temps env');
              fn_body = (Ssequence (stmt', (Scall (None, (Evar (start_id,
              (type_of_function start_f))), [])))) }, env')
            | None -> None)
         | PA.STAccept ->
           Some ({ fn_return = Tvoid; fn_callconv = { cc_vararg = None;
             cc_unproto = true; cc_structret = true }; fn_params = params0;
             fn_vars = (get_vars env'); fn_temps = (get_temps env');
             fn_body = (Ssequence (stmt', (Sreturn None))) }, env')
         | PA.STReject -> None
         | PA.STName x ->
           (match lookup_function env' x with
            | Some p0 ->
              let (x_f, x_id) = p0 in
              Some ({ fn_return = Tvoid; fn_callconv = { cc_vararg = None;
              cc_unproto = true; cc_structret = true }; fn_params = params0;
              fn_vars = (get_vars env'); fn_temps = (get_temps env');
              fn_body = (Ssequence (stmt', (Scall (None, (Evar (x_id,
              (type_of_function x_f))), [])))) }, env')
            | None -> None))
      | PA.PSelect (_, _, _, _) -> None)
   | None -> None)

(** val coq_CTranslateParams :
    E.params -> coq_ClightEnv -> (ident * coq_type) list * coq_ClightEnv **)

let coq_CTranslateParams params0 env =
  fold_left (fun cumulator p ->
    let (l, env') = cumulator in
    let (env'0, new_id) = new_ident env' in
    let (ct0, env_ct) =
      let (_, p0) = p in
      (match p0 with
       | P.PAIn x -> coq_CTranslateType x env'0
       | P.PAOut x ->
         let (ct', env_ct') = coq_CTranslateType x env'0 in
         ((Tpointer (ct', noattr)), env_ct')
       | P.PAInOut x ->
         let (ct', env_ct') = coq_CTranslateType x env'0 in
         ((Tpointer (ct', noattr)), env_ct'))
    in
    let s0 = fst p in
    let env_temp_added = add_temp_arg env_ct s0 ct0 new_id in
    (((new_id, ct0) :: l), env_temp_added)) params0 ([], env)

(** val coq_CCopyIn :
    E.params -> coq_ClightEnv -> statement * coq_ClightEnv **)

let coq_CCopyIn fn_params0 env =
  fold_left (fun cumulator fn_param ->
    let (name, t0) = fn_param in
    let (prev_stmt, prev_env) = cumulator in
    (match find_ident_temp_arg env name with
     | Some p ->
       let (oldid, tempid) = p in
       (match t0 with
        | P.PAIn t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (tempid, ct0)), (Evar (oldid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct)
        | P.PAOut t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (tempid, ct0)), (Evar (oldid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct)
        | P.PAInOut t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (tempid, ct0)), (Evar (oldid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct))
     | None -> cumulator)) fn_params0 (Sskip, env)

(** val coq_CCopyOut :
    E.params -> coq_ClightEnv -> statement * coq_ClightEnv **)

let coq_CCopyOut fn_params0 env =
  fold_left (fun cumulator fn_param ->
    let (name, t0) = fn_param in
    let (prev_stmt, prev_env) = cumulator in
    (match find_ident_temp_arg env name with
     | Some p ->
       let (oldid, tempid) = p in
       (match t0 with
        | P.PAIn t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (oldid, ct0)), (Evar (tempid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct)
        | P.PAOut t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (oldid, ct0)), (Evar (tempid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct)
        | P.PAInOut t1 ->
          let (ct0, env_ct) = coq_CTranslateType t1 prev_env in
          let new_stmt = Sassign ((Evar (oldid, ct0)), (Evar (tempid, ct0)))
          in
          ((Ssequence (prev_stmt, new_stmt)), env_ct))
     | None -> cumulator)) fn_params0 (Sskip, env)

(** val coq_CTranslateArrow :
    E.arrowT -> coq_ClightEnv -> ((ident * coq_type)
    list * coq_type) * coq_ClightEnv **)

let coq_CTranslateArrow signature env =
  let P.Arrow (pas, ret) = signature in
  let (fn_params0, env_params_created) = coq_CTranslateParams pas env in
  (match ret with
   | Some return_t ->
     let (ct0, env_ct) = coq_CTranslateType return_t env_params_created in
     ((fn_params0, ct0), env_ct)
   | None -> ((fn_params0, Tvoid), env_params_created))

(** val coq_PaFromArrow : E.arrowT -> E.params **)

let coq_PaFromArrow = function
| P.Arrow (pas, _) -> pas

(** val coq_CTranslateTopParser :
    'a1 TD.d -> coq_ClightEnv -> coq_ClightEnv option **)

let coq_CTranslateTopParser parsr env =
  match parsr with
  | TD.TPParser (p, _, params0, st, states, _) ->
    let (fn_params0, env0) = coq_CTranslateParams params0 env in
    let (copyin, env1) = coq_CCopyIn params0 env0 in
    let (copyout, env2) = coq_CCopyOut params0 env1 in
    let state_names = F.keys states in
    let env_fn_sig_declared =
      let fn_sig = { fn_return = Tvoid; fn_callconv = { cc_vararg = None;
        cc_unproto = true; cc_structret = true }; fn_params = fn_params0;
        fn_vars = []; fn_temps = []; fn_body = Sskip }
      in
      let env_start_fn_sig_declared =
        add_function env2 ('s'::('t'::('a'::('r'::('t'::[]))))) fn_sig
      in
      fold_left (fun cumulator state_name ->
        add_function cumulator state_name fn_sig) state_names
        env_start_fn_sig_declared
    in
    let env_fn_declared =
      fold_left (fun cumulator state_name ->
        match cumulator with
        | Some env' ->
          (match Env.find coq_StringEqDec state_name states with
           | Some sb ->
             (match coq_CTranslateParserState sb env' fn_params0 with
              | Some p0 ->
                let (f0, _) = p0 in Some (update_function env' state_name f0)
              | None -> None)
           | None -> None)
        | None -> None) state_names (Some env_fn_sig_declared)
    in
    (match env_fn_declared with
     | Some env_fn_declared0 ->
       (match coq_CTranslateParserState st env_fn_declared0 fn_params0 with
        | Some p0 ->
          let (f_start, _) = p0 in
          let env_start_declared =
            add_function env_fn_declared0
              ('s'::('t'::('a'::('r'::('t'::[]))))) f_start
          in
          (match lookup_function env_start_declared
                   ('s'::('t'::('a'::('r'::('t'::[]))))) with
           | Some p1 ->
             let (start_f, start_id) = p1 in
             let fn_body0 = Ssequence (copyin, (Ssequence ((Scall (None,
               (Evar (start_id, (type_of_function start_f))), [])), copyout)))
             in
             let top_function = { fn_return = Tvoid; fn_callconv =
               { cc_vararg = None; cc_unproto = true; cc_structret = true };
               fn_params = fn_params0; fn_vars = []; fn_temps = []; fn_body =
               fn_body0 }
             in
             let env_topfn_added =
               add_function env_start_declared p top_function
             in
             Some env_topfn_added
           | None -> None)
        | None -> None)
     | None -> None)
  | _ -> None

(** val coq_CTranslateAction :
    E.params -> 'a1 ST.s -> coq_ClightEnv -> (ident * coq_type) list ->
    E.params -> coq_function option **)

let coq_CTranslateAction signature body env top_fn_params top_signature =
  let (fn_params0, env_params_created) = coq_CTranslateParams signature env in
  let fn_params1 = app top_fn_params fn_params0 in
  let full_signature = app top_signature signature in
  let (copyin, env_copyin) = coq_CCopyIn full_signature env_params_created in
  let (copyout, env_copyout) = coq_CCopyOut full_signature env_copyin in
  (match coq_CTranslateStatement body env_copyout with
   | Some p ->
     let (c_body, env_body_translated) = p in
     let body0 = Ssequence (copyin, (Ssequence (c_body, copyout))) in
     Some { fn_return = Tvoid; fn_callconv = { cc_vararg = None; cc_unproto =
     true; cc_structret = true }; fn_params = fn_params1; fn_vars =
     (get_vars env_body_translated); fn_temps =
     (get_temps env_body_translated); fn_body = body0 }
   | None -> None)

(** val coq_CTranslateControlLocalDeclaration :
    'a1 CT.ControlDecl.d -> coq_ClightEnv -> (ident * coq_type) list ->
    E.params -> coq_ClightEnv option **)

let rec coq_CTranslateControlLocalDeclaration ct0 env top_fn_params top_signature =
  match ct0 with
  | CT.ControlDecl.CDAction (a, params0, body, _) ->
    (match coq_CTranslateAction params0 body env top_fn_params top_signature with
     | Some f0 -> Some (add_function env a f0)
     | None -> None)
  | CT.ControlDecl.CDTable (_, _, _) -> Some env
  | CT.ControlDecl.CDSeq (d1, d2, _) ->
    (match coq_CTranslateControlLocalDeclaration d1 env top_fn_params
             top_signature with
     | Some env1 ->
       coq_CTranslateControlLocalDeclaration d2 env1 top_fn_params
         top_signature
     | None -> None)

(** val coq_CTranslateTopControl :
    'a1 TD.d -> coq_ClightEnv -> coq_ClightEnv option **)

let coq_CTranslateTopControl ctrl env =
  match ctrl with
  | TD.TPControl (c, _, params0, body, blk, _) ->
    let (fn_params0, env_top_fn_param) = coq_CTranslateParams params0 env in
    let (copyin, env_copyin) = coq_CCopyIn params0 env_top_fn_param in
    let (copyout, env_copyout) = coq_CCopyOut params0 env_copyin in
    (match coq_CTranslateControlLocalDeclaration body env_copyout fn_params0
             params0 with
     | Some env_local_decled ->
       (match coq_CTranslateStatement blk env_local_decled with
        | Some p ->
          let (apply_blk, env_apply_block_translated) = p in
          let body0 = Ssequence (copyin, (Ssequence (apply_blk, copyout))) in
          let top_fn = { fn_return = Tvoid; fn_callconv = { cc_vararg = None;
            cc_unproto = true; cc_structret = true }; fn_params = fn_params0;
            fn_vars = (get_vars env_apply_block_translated); fn_temps =
            (get_temps env_apply_block_translated); fn_body = body0 }
          in
          let env_top_fn_declared = add_function env_local_decled c top_fn in
          Some env_top_fn_declared
        | None -> None)
     | None -> None)
  | _ -> None

(** val coq_CTranslateFunction :
    'a1 TD.d -> coq_ClightEnv -> coq_ClightEnv option **)

let coq_CTranslateFunction funcdecl env =
  match funcdecl with
  | TD.TPFunction (name, signature, body, _) ->
    let (p, env_params_created) = coq_CTranslateArrow signature env in
    let (fn_params0, fn_return0) = p in
    let paramargs = coq_PaFromArrow signature in
    let (copyin, env_copyin) = coq_CCopyIn paramargs env_params_created in
    let (copyout, env_copyout) = coq_CCopyOut paramargs env_copyin in
    (match coq_CTranslateStatement body env_copyout with
     | Some p0 ->
       let (c_body, env_body_translated) = p0 in
       let body0 = Ssequence (copyin, (Ssequence (c_body, copyout))) in
       let top_function = { fn_return = fn_return0; fn_callconv =
         { cc_vararg = None; cc_unproto = true; cc_structret = true };
         fn_params = fn_params0; fn_vars = (get_vars env_body_translated);
         fn_temps = (get_temps env_body_translated); fn_body = body0 }
       in
       Some (add_function env_params_created name top_function)
     | None -> None)
  | _ -> None

(** val coq_CTranslateTopDeclaration :
    'a1 P4cub.TopDecl.d -> coq_ClightEnv -> coq_ClightEnv option **)

let rec coq_CTranslateTopDeclaration d0 env =
  match d0 with
  | P4cub.TopDecl.TPInstantiate (_, _, _, _) -> Some env
  | P4cub.TopDecl.TPControl (_, _, _, _, _, _) ->
    coq_CTranslateTopControl d0 env
  | P4cub.TopDecl.TPParser (_, _, _, _, _, _) ->
    coq_CTranslateTopParser d0 env
  | P4cub.TopDecl.TPFunction (_, _, _, _) -> coq_CTranslateFunction d0 env
  | P4cub.TopDecl.TPSeq (d1, d2, _) ->
    (match coq_CTranslateTopDeclaration d1 env with
     | Some env1 -> coq_CTranslateTopDeclaration d2 env1
     | None -> None)
  | _ -> None

(** val coq_Compile : 'a1 P4cub.TopDecl.d -> Clight.program res **)

let coq_Compile prog =
  let main_decl = Gfun (Internal { fn_return = Tvoid; fn_callconv =
    { cc_vararg = None; cc_unproto = true; cc_structret = true }; fn_params =
    []; fn_vars = []; fn_temps = []; fn_body = Sskip })
  in
  let (init_env, main_id) = new_ident newClightEnv in
  (match coq_CTranslateTopDeclaration prog init_env with
   | Some env_all_declared ->
     (match get_functions env_all_declared with
      | Some f_decls ->
        let f_decls0 =
          map (fun x -> let (id, f0) = x in (id, (Gfun (Internal f0))))
            f_decls
        in
        let typ_decls = get_composites env_all_declared in
        make_program typ_decls ((main_id, main_decl) :: f_decls0) [] main_id
      | None ->
        Error
          (msg
            ('c'::('a'::('n'::('\''::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('a'::('l'::('l'::(' '::('t'::('h'::('e'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::[])))))))))))))))))))))))))))))))))))))))
   | None ->
     Error
       (msg
         ('s'::('o'::('m'::('e'::('t'::('h'::('i'::('n'::('g'::(' '::('w'::('e'::('n'::('t'::(' '::('w'::('r'::('o'::('n'::('g'::[]))))))))))))))))))))))

(** val coq_Compile_print : 'a1 P4cub.TopDecl.d -> unit **)

let coq_Compile_print prog =
  match coq_Compile prog with
  | OK prog0 -> print_Clight prog0
  | Error _ -> ()

(** val test : Clight.program res **)

let test =
  coq_Compile helloworld_program
