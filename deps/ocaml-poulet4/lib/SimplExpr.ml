open Datatypes
open List
open P4String
open Syntax
open Typed

(** val to_digit : Bigint.t -> char **)

let to_digit = (fun x -> Char.chr 20)

(** val to_N_aux : int -> Bigint.t -> string -> string **)

let rec to_N_aux = (fun x y z -> z)

(** val coq_N_to_string : Bigint.t -> string **)

let coq_N_to_string = (fun x -> Z.to_string (Bigint.to_zarith_bigint x))

(** val add1 : Bigint.t -> Bigint.t **)

let add1 = (fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))

(** val coq_N_to_tempvar : 'a1 -> Bigint.t -> 'a1 t **)

let coq_N_to_tempvar default_tag n =
  { tags = default_tag; str = ((^) "t'" (coq_N_to_string n)) }

(** val transform_ept :
    'a1 -> Bigint.t -> 'a1 coq_ExpressionPreT -> 'a1 -> 'a1 coq_P4Type ->
    direction -> (('a1 t * 'a1 coq_Expression) list * 'a1
    coq_Expression) * Bigint.t **)

let transform_ept default_tag =
  let rec transform_ept0 nameIdx exp tag typ dir =
    match exp with
    | ExpArrayAccess (array, index) ->
      let (l1e1, n1) = transform_exp0 nameIdx array in
      let (l2e2, n2) = transform_exp0 n1 index in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpArrayAccess (e1, e2)), typ,
      dir))), n2)
    | ExpBitStringAccess (bits, lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx bits in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpBitStringAccess (e1, lo, hi)), typ,
      dir))), n1)
    | ExpList value ->
      let (l1e1, n1) =
        let rec transform_list0 idx = function
        | [] -> (([], []), idx)
        | exp0 :: rest ->
          let (l2e2, n2) = transform_exp0 idx exp0 in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_list0 n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_list0 nameIdx value
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpList e1), typ, dir))), n1)
    | ExpRecord entries ->
      let (l1e1, n1) =
        let rec transform_lkv idx = function
        | [] -> (([], []), idx)
        | kv :: rest ->
          let (l2e2, n2) = transform_keyvalue0 idx kv in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_lkv n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_lkv nameIdx entries
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpRecord e1), typ, dir))), n1)
    | ExpUnaryOp (op, arg) ->
      let (l1e1, n1) = transform_exp0 nameIdx arg in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpUnaryOp (op, e1)), typ, dir))), n1)
    | ExpBinaryOp (op, args) ->
      let (arg1, arg2) = args in
      let (l1e1, n1) = transform_exp0 nameIdx arg1 in
      let (l2e2, n2) = transform_exp0 n1 arg2 in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpBinaryOp (op, (e1, e2))), typ,
      dir))), n2)
    | ExpCast (typ', expr) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpCast (typ', e1)), typ, dir))), n1)
    | ExpExpressionMember (expr, name) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpExpressionMember (e1, name)), typ,
      dir))), n1)
    | ExpTernary (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp0 nameIdx cond in
      let (l2e2, n2) = transform_exp0 n1 tru in
      let (l3e3, n3) = transform_exp0 n2 fls in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      let (l3, e3) = l3e3 in
      (((app l1 (app l2 l3)), (MkExpression (tag, (ExpTernary (e1, e2, e3)),
      typ, dir))), n3)
    | ExpFunctionCall (func, type_args, args) ->
      let (l1e1, n1) =
        let rec transform_lopt idx = function
        | [] -> (([], []), idx)
        | o :: rest ->
          (match o with
           | Some exp0 ->
             let (l2e2, n2) = transform_exp0 idx exp0 in
             let (l2, e2) = l2e2 in
             let (l3e3, n3) = transform_lopt n2 rest in
             let (l3, el3) = l3e3 in (((app l2 l3), ((Some e2) :: el3)), n3)
           | None ->
             let (l2e2, n2) = transform_lopt idx rest in
             let (l2, e2) = l2e2 in ((l2, (None :: e2)), n2))
        in transform_lopt nameIdx args
      in
      let (l1, e1) = l1e1 in
      (((app l1 (((coq_N_to_tempvar default_tag n1), (MkExpression (tag,
          (ExpFunctionCall (func, type_args, e1)), typ, dir))) :: [])),
      (MkExpression (tag, (ExpName (BareName
      (coq_N_to_tempvar default_tag n1))), typ, dir))), (add1 n1))
    | ExpNamelessInstantiation (typ', args) ->
      (((((coq_N_to_tempvar default_tag nameIdx), (MkExpression (tag,
        (ExpNamelessInstantiation (typ', args)), typ, dir))) :: []),
        (MkExpression (tag, (ExpName (BareName
        (coq_N_to_tempvar default_tag nameIdx))), typ, dir))), (add1 nameIdx))
    | ExpMask (expr, mask) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l2e2, n2) = transform_exp0 n1 mask in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpMask (e1, e2)), typ, dir))), n2)
    | ExpRange (lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx lo in
      let (l2e2, n2) = transform_exp0 n1 hi in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpRange (e1, e2)), typ, dir))), n2)
    | x -> (([], (MkExpression (tag, x, typ, dir))), nameIdx)
  and transform_exp0 nameIdx = function
  | MkExpression (tag, expr, typ, dir) ->
    transform_ept0 nameIdx expr tag typ dir
  and transform_keyvalue0 nameIdx = function
  | MkKeyValue (tags0, key, value) ->
    let (l1e1, n1) = transform_exp0 nameIdx value in
    let (l1, e1) = l1e1 in ((l1, (MkKeyValue (tags0, key, e1))), n1)
  in transform_ept0

(** val transform_exp :
    'a1 -> Bigint.t -> 'a1 coq_Expression -> (('a1 t * 'a1 coq_Expression)
    list * 'a1 coq_Expression) * Bigint.t **)

let transform_exp default_tag =
  let rec transform_ept0 nameIdx exp tag typ dir =
    match exp with
    | ExpBool b ->
      (([], (MkExpression (tag, (ExpBool b), typ, dir))), nameIdx)
    | ExpInt i -> (([], (MkExpression (tag, (ExpInt i), typ, dir))), nameIdx)
    | ExpString str0 ->
      (([], (MkExpression (tag, (ExpString str0), typ, dir))), nameIdx)
    | ExpName name ->
      (([], (MkExpression (tag, (ExpName name), typ, dir))), nameIdx)
    | ExpArrayAccess (array, index) ->
      let (l1e1, n1) = transform_exp0 nameIdx array in
      let (l2e2, n2) = transform_exp0 n1 index in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpArrayAccess (e1, e2)), typ,
      dir))), n2)
    | ExpBitStringAccess (bits, lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx bits in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpBitStringAccess (e1, lo, hi)), typ,
      dir))), n1)
    | ExpList value ->
      let (l1e1, n1) =
        let rec transform_list0 idx = function
        | [] -> (([], []), idx)
        | exp0 :: rest ->
          let (l2e2, n2) = transform_exp0 idx exp0 in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_list0 n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_list0 nameIdx value
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpList e1), typ, dir))), n1)
    | ExpRecord entries ->
      let (l1e1, n1) =
        let rec transform_lkv idx = function
        | [] -> (([], []), idx)
        | kv :: rest ->
          let (l2e2, n2) = transform_keyvalue0 idx kv in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_lkv n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_lkv nameIdx entries
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpRecord e1), typ, dir))), n1)
    | ExpUnaryOp (op, arg) ->
      let (l1e1, n1) = transform_exp0 nameIdx arg in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpUnaryOp (op, e1)), typ, dir))), n1)
    | ExpBinaryOp (op, args) ->
      let (arg1, arg2) = args in
      let (l1e1, n1) = transform_exp0 nameIdx arg1 in
      let (l2e2, n2) = transform_exp0 n1 arg2 in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpBinaryOp (op, (e1, e2))), typ,
      dir))), n2)
    | ExpCast (typ', expr) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpCast (typ', e1)), typ, dir))), n1)
    | ExpTypeMember (typ', name) ->
      (([], (MkExpression (tag, (ExpTypeMember (typ', name)), typ, dir))),
        nameIdx)
    | ExpErrorMember mem ->
      (([], (MkExpression (tag, (ExpErrorMember mem), typ, dir))), nameIdx)
    | ExpExpressionMember (expr, name) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpExpressionMember (e1, name)), typ,
      dir))), n1)
    | ExpTernary (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp0 nameIdx cond in
      let (l2e2, n2) = transform_exp0 n1 tru in
      let (l3e3, n3) = transform_exp0 n2 fls in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      let (l3, e3) = l3e3 in
      (((app l1 (app l2 l3)), (MkExpression (tag, (ExpTernary (e1, e2, e3)),
      typ, dir))), n3)
    | ExpFunctionCall (func, type_args, args) ->
      let (l1e1, n1) =
        let rec transform_lopt idx = function
        | [] -> (([], []), idx)
        | o :: rest ->
          (match o with
           | Some exp0 ->
             let (l2e2, n2) = transform_exp0 idx exp0 in
             let (l2, e2) = l2e2 in
             let (l3e3, n3) = transform_lopt n2 rest in
             let (l3, el3) = l3e3 in (((app l2 l3), ((Some e2) :: el3)), n3)
           | None ->
             let (l2e2, n2) = transform_lopt idx rest in
             let (l2, e2) = l2e2 in ((l2, (None :: e2)), n2))
        in transform_lopt nameIdx args
      in
      let (l1, e1) = l1e1 in
      (((app l1 (((coq_N_to_tempvar default_tag n1), (MkExpression (tag,
          (ExpFunctionCall (func, type_args, e1)), typ, dir))) :: [])),
      (MkExpression (tag, (ExpName (BareName
      (coq_N_to_tempvar default_tag n1))), typ, dir))), (add1 n1))
    | ExpNamelessInstantiation (typ', args) ->
      (((((coq_N_to_tempvar default_tag nameIdx), (MkExpression (tag,
        (ExpNamelessInstantiation (typ', args)), typ, dir))) :: []),
        (MkExpression (tag, (ExpName (BareName
        (coq_N_to_tempvar default_tag nameIdx))), typ, dir))), (add1 nameIdx))
    | ExpDontCare ->
      (([], (MkExpression (tag, ExpDontCare, typ, dir))), nameIdx)
    | ExpMask (expr, mask) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l2e2, n2) = transform_exp0 n1 mask in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpMask (e1, e2)), typ, dir))), n2)
    | ExpRange (lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx lo in
      let (l2e2, n2) = transform_exp0 n1 hi in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpRange (e1, e2)), typ, dir))), n2)
  and transform_exp0 nameIdx = function
  | MkExpression (tag, expr, typ, dir) ->
    transform_ept0 nameIdx expr tag typ dir
  and transform_keyvalue0 nameIdx = function
  | MkKeyValue (tags0, key, value) ->
    let (l1e1, n1) = transform_exp0 nameIdx value in
    let (l1, e1) = l1e1 in ((l1, (MkKeyValue (tags0, key, e1))), n1)
  in transform_exp0

(** val transform_keyvalue :
    'a1 -> Bigint.t -> 'a1 coq_KeyValue -> (('a1 t * 'a1 coq_Expression)
    list * 'a1 coq_KeyValue) * Bigint.t **)

let transform_keyvalue default_tag =
  let rec transform_ept0 nameIdx exp tag typ dir =
    match exp with
    | ExpBool b ->
      (([], (MkExpression (tag, (ExpBool b), typ, dir))), nameIdx)
    | ExpInt i -> (([], (MkExpression (tag, (ExpInt i), typ, dir))), nameIdx)
    | ExpString str0 ->
      (([], (MkExpression (tag, (ExpString str0), typ, dir))), nameIdx)
    | ExpName name ->
      (([], (MkExpression (tag, (ExpName name), typ, dir))), nameIdx)
    | ExpArrayAccess (array, index) ->
      let (l1e1, n1) = transform_exp0 nameIdx array in
      let (l2e2, n2) = transform_exp0 n1 index in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpArrayAccess (e1, e2)), typ,
      dir))), n2)
    | ExpBitStringAccess (bits, lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx bits in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpBitStringAccess (e1, lo, hi)), typ,
      dir))), n1)
    | ExpList value ->
      let (l1e1, n1) =
        let rec transform_list0 idx = function
        | [] -> (([], []), idx)
        | exp0 :: rest ->
          let (l2e2, n2) = transform_exp0 idx exp0 in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_list0 n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_list0 nameIdx value
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpList e1), typ, dir))), n1)
    | ExpRecord entries ->
      let (l1e1, n1) =
        let rec transform_lkv idx = function
        | [] -> (([], []), idx)
        | kv :: rest ->
          let (l2e2, n2) = transform_keyvalue0 idx kv in
          let (l2, e2) = l2e2 in
          let (l3e3, n3) = transform_lkv n2 rest in
          let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)
        in transform_lkv nameIdx entries
      in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpRecord e1), typ, dir))), n1)
    | ExpUnaryOp (op, arg) ->
      let (l1e1, n1) = transform_exp0 nameIdx arg in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpUnaryOp (op, e1)), typ, dir))), n1)
    | ExpBinaryOp (op, args) ->
      let (arg1, arg2) = args in
      let (l1e1, n1) = transform_exp0 nameIdx arg1 in
      let (l2e2, n2) = transform_exp0 n1 arg2 in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpBinaryOp (op, (e1, e2))), typ,
      dir))), n2)
    | ExpCast (typ', expr) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpCast (typ', e1)), typ, dir))), n1)
    | ExpTypeMember (typ', name) ->
      (([], (MkExpression (tag, (ExpTypeMember (typ', name)), typ, dir))),
        nameIdx)
    | ExpErrorMember mem ->
      (([], (MkExpression (tag, (ExpErrorMember mem), typ, dir))), nameIdx)
    | ExpExpressionMember (expr, name) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l1, e1) = l1e1 in
      ((l1, (MkExpression (tag, (ExpExpressionMember (e1, name)), typ,
      dir))), n1)
    | ExpTernary (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp0 nameIdx cond in
      let (l2e2, n2) = transform_exp0 n1 tru in
      let (l3e3, n3) = transform_exp0 n2 fls in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      let (l3, e3) = l3e3 in
      (((app l1 (app l2 l3)), (MkExpression (tag, (ExpTernary (e1, e2, e3)),
      typ, dir))), n3)
    | ExpFunctionCall (func, type_args, args) ->
      let (l1e1, n1) =
        let rec transform_lopt idx = function
        | [] -> (([], []), idx)
        | o :: rest ->
          (match o with
           | Some exp0 ->
             let (l2e2, n2) = transform_exp0 idx exp0 in
             let (l2, e2) = l2e2 in
             let (l3e3, n3) = transform_lopt n2 rest in
             let (l3, el3) = l3e3 in (((app l2 l3), ((Some e2) :: el3)), n3)
           | None ->
             let (l2e2, n2) = transform_lopt idx rest in
             let (l2, e2) = l2e2 in ((l2, (None :: e2)), n2))
        in transform_lopt nameIdx args
      in
      let (l1, e1) = l1e1 in
      (((app l1 (((coq_N_to_tempvar default_tag n1), (MkExpression (tag,
          (ExpFunctionCall (func, type_args, e1)), typ, dir))) :: [])),
      (MkExpression (tag, (ExpName (BareName
      (coq_N_to_tempvar default_tag n1))), typ, dir))), (add1 n1))
    | ExpNamelessInstantiation (typ', args) ->
      (((((coq_N_to_tempvar default_tag nameIdx), (MkExpression (tag,
        (ExpNamelessInstantiation (typ', args)), typ, dir))) :: []),
        (MkExpression (tag, (ExpName (BareName
        (coq_N_to_tempvar default_tag nameIdx))), typ, dir))), (add1 nameIdx))
    | ExpDontCare ->
      (([], (MkExpression (tag, ExpDontCare, typ, dir))), nameIdx)
    | ExpMask (expr, mask) ->
      let (l1e1, n1) = transform_exp0 nameIdx expr in
      let (l2e2, n2) = transform_exp0 n1 mask in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpMask (e1, e2)), typ, dir))), n2)
    | ExpRange (lo, hi) ->
      let (l1e1, n1) = transform_exp0 nameIdx lo in
      let (l2e2, n2) = transform_exp0 n1 hi in
      let (l1, e1) = l1e1 in
      let (l2, e2) = l2e2 in
      (((app l1 l2), (MkExpression (tag, (ExpRange (e1, e2)), typ, dir))), n2)
  and transform_exp0 nameIdx = function
  | MkExpression (tag, expr, typ, dir) ->
    transform_ept0 nameIdx expr tag typ dir
  and transform_keyvalue0 nameIdx = function
  | MkKeyValue (tags0, key, value) ->
    let (l1e1, n1) = transform_exp0 nameIdx value in
    let (l1, e1) = l1e1 in ((l1, (MkKeyValue (tags0, key, e1))), n1)
  in transform_keyvalue0

(** val transform_Expr :
    'a1 -> Bigint.t -> 'a1 coq_Expression -> (('a1 t * 'a1 coq_Expression)
    list * 'a1 coq_Expression) * Bigint.t **)

let transform_Expr default_tag nameIdx exp = match exp with
| MkExpression (_, expr, _, _) ->
  (match expr with
   | ExpFunctionCall (_, _, _) -> (([], exp), nameIdx)
   | _ -> transform_exp default_tag nameIdx exp)

(** val expr_to_stmt :
    'a1 -> coq_StmType -> ('a1 t * 'a1 coq_Expression) -> 'a1 coq_Statement **)

let expr_to_stmt tags0 typ = function
| (name, e) ->
  let MkExpression (tag, expr, typ', dir) = e in
  (match expr with
   | ExpNamelessInstantiation (typ'', e1) ->
     MkStatement (tags0, (StatInstantiation (typ'', e1, name, None)), typ)
   | _ ->
     MkStatement (tags0, (StatVariable (typ', name, (Some (MkExpression (tag,
       expr, typ', dir))))), typ))

(** val to_StmtList :
    'a1 -> coq_StmType -> ('a1 t * 'a1 coq_Expression) list -> 'a1
    coq_Statement list **)

let to_StmtList tags0 typ nel =
  map (expr_to_stmt tags0 typ) nel

(** val transform_list :
    (Bigint.t -> 'a1 -> ('a2 list * 'a3) * Bigint.t) -> Bigint.t -> 'a1 list
    -> ('a2 list * 'a3 list) * Bigint.t **)

let rec transform_list f idx = function
| [] -> (([], []), idx)
| exp :: rest ->
  let (l2e2, n2) = f idx exp in
  let (l2, e2) = l2e2 in
  let (l3e3, n3) = transform_list f n2 rest in
  let (l3, el3) = l3e3 in (((app l2 l3), (e2 :: el3)), n3)

(** val transform_exprs :
    'a1 -> Bigint.t -> 'a1 coq_Expression list -> (('a1 t * 'a1
    coq_Expression) list * 'a1 coq_Expression list) * Bigint.t **)

let transform_exprs default_tag idx l =
  transform_list (transform_exp default_tag) idx l

(** val prepend_to_block :
    'a1 coq_Statement list -> 'a1 coq_Block -> 'a1 coq_Block **)

let rec prepend_to_block l blk =
  match l with
  | [] -> blk
  | x :: rest -> BlockCons (x, (prepend_to_block rest blk))

(** val transform_exp_stmt :
    'a1 -> Bigint.t -> 'a1 coq_Expression -> ('a1 coq_Statement list * 'a1
    coq_Expression) * Bigint.t **)

let transform_exp_stmt default_tag nameIdx exp =
  let (l1e1, n1) = transform_exp default_tag nameIdx exp in
  let (l1, e1) = l1e1 in
  let stl1 = to_StmtList default_tag StmVoid l1 in ((stl1, e1), n1)

(** val transform_Expr_stmt :
    'a1 -> Bigint.t -> 'a1 coq_Expression -> ('a1 coq_Statement list * 'a1
    coq_Expression) * Bigint.t **)

let transform_Expr_stmt default_tag nameIdx exp =
  let (l1e1, n1) = transform_Expr default_tag nameIdx exp in
  let (l1, e1) = l1e1 in
  let stl1 = to_StmtList default_tag StmVoid l1 in ((stl1, e1), n1)

(** val transform_list_stmt :
    'a1 -> Bigint.t -> 'a1 coq_Expression list -> ('a1 coq_Statement
    list * 'a1 coq_Expression list) * Bigint.t **)

let transform_list_stmt default_tag nameIdx l =
  let (l1e1, n1) = transform_exprs default_tag nameIdx l in
  let (l1, e1) = l1e1 in
  let stl1 = to_StmtList default_tag StmVoid l1 in ((stl1, e1), n1)

(** val transform_stmtpt :
    'a1 -> Bigint.t -> 'a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a1
    coq_Statement list * Bigint.t **)

let transform_stmtpt default_tag =
  let rec transform_stmtpt0 nameIdx tags0 stmt typ =
    match stmt with
    | StatAssignment (lhs, rhs) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx lhs in
      let (l1, e1) = l1e1 in
      let (l2e2, n2) = transform_Expr_stmt default_tag n1 rhs in
      let (l2, e2) = l2e2 in
      ((app l1
         (app l2 ((MkStatement (tags0, (StatAssignment (e1, e2)),
           typ)) :: []))), n2)
    | StatDirectApplication (typ', args) ->
      let (l1e1, n1) = transform_list_stmt default_tag nameIdx args in
      let (l1, e1) = l1e1 in
      ((app l1 ((MkStatement (tags0, (StatDirectApplication (typ', e1)),
         typ)) :: [])), n1)
    | StatConditional (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx cond in
      let (l1, _) = l1e1 in
      let (stl2, n2) = transform_stmt0 n1 tru in
      let (stl3, n3) =
        match fls with
        | Some stmt' -> transform_stmt0 n2 stmt'
        | None -> ([], n2)
      in
      ((app l1 (app stl2 stl3)), n3)
    | StatBlock block ->
      let (blk, n1) = transform_blk0 nameIdx block in
      (((MkStatement (tags0, (StatBlock blk), typ)) :: []), n1)
    | StatExit -> (((MkStatement (tags0, StatExit, typ)) :: []), nameIdx)
    | StatEmpty -> (((MkStatement (tags0, StatEmpty, typ)) :: []), nameIdx)
    | StatReturn expr0 ->
      (match expr0 with
       | Some expr ->
         let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatReturn (Some e1)), typ)) :: [])),
         n1)
       | None ->
         (((MkStatement (tags0, (StatReturn None), typ)) :: []), nameIdx))
    | StatSwitch (expr, cases) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
      let (l1, e1) = l1e1 in
      let (caseList, n2) =
        let rec transform_lssc idx = function
        | [] -> ([], idx)
        | x :: rest ->
          let (c1, n3) = transform_ssc0 idx x in
          let (rest', n4) = transform_lssc n3 rest in ((c1 :: rest'), n4)
        in transform_lssc n1 cases
      in
      ((app l1 ((MkStatement (tags0, (StatSwitch (e1, caseList)),
         typ)) :: [])), n2)
    | StatVariable (typ', name, init) ->
      (match init with
       | Some expr ->
         let (l1e1, n1) = transform_Expr_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatVariable (typ', name, (Some
            e1))), typ)) :: [])), n1)
       | None -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx))
    | _ -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
  and transform_stmt0 nameIdx = function
  | MkStatement (tags0, stmt0, typ) ->
    transform_stmtpt0 nameIdx tags0 stmt0 typ
  and transform_blk0 nameIdx = function
  | BlockEmpty tag -> ((BlockEmpty tag), nameIdx)
  | BlockCons (stmt, blk') ->
    let (stl1, n1) = transform_stmt0 nameIdx stmt in
    let (blk2, n2) = transform_blk0 n1 blk' in
    ((prepend_to_block stl1 blk2), n2)
  and transform_ssc0 nameIdx ssc = match ssc with
  | StatSwCaseAction (tags0, label, code) ->
    let (blk, n1) = transform_blk0 nameIdx code in
    ((StatSwCaseAction (tags0, label, blk)), n1)
  | StatSwCaseFallThrough (_, _) -> (ssc, nameIdx)
  in transform_stmtpt0

(** val transform_stmt :
    'a1 -> Bigint.t -> 'a1 coq_Statement -> 'a1 coq_Statement list * Bigint.t **)

let transform_stmt default_tag =
  let rec transform_stmtpt0 nameIdx tags0 stmt typ =
    match stmt with
    | StatMethodCall (_, _, _) ->
      (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
    | StatAssignment (lhs, rhs) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx lhs in
      let (l1, e1) = l1e1 in
      let (l2e2, n2) = transform_Expr_stmt default_tag n1 rhs in
      let (l2, e2) = l2e2 in
      ((app l1
         (app l2 ((MkStatement (tags0, (StatAssignment (e1, e2)),
           typ)) :: []))), n2)
    | StatDirectApplication (typ', args) ->
      let (l1e1, n1) = transform_list_stmt default_tag nameIdx args in
      let (l1, e1) = l1e1 in
      ((app l1 ((MkStatement (tags0, (StatDirectApplication (typ', e1)),
         typ)) :: [])), n1)
    | StatConditional (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx cond in
      let (l1, _) = l1e1 in
      let (stl2, n2) = transform_stmt0 n1 tru in
      let (stl3, n3) =
        match fls with
        | Some stmt' -> transform_stmt0 n2 stmt'
        | None -> ([], n2)
      in
      ((app l1 (app stl2 stl3)), n3)
    | StatBlock block ->
      let (blk, n1) = transform_blk0 nameIdx block in
      (((MkStatement (tags0, (StatBlock blk), typ)) :: []), n1)
    | StatExit -> (((MkStatement (tags0, StatExit, typ)) :: []), nameIdx)
    | StatEmpty -> (((MkStatement (tags0, StatEmpty, typ)) :: []), nameIdx)
    | StatReturn expr0 ->
      (match expr0 with
       | Some expr ->
         let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatReturn (Some e1)), typ)) :: [])),
         n1)
       | None ->
         (((MkStatement (tags0, (StatReturn None), typ)) :: []), nameIdx))
    | StatSwitch (expr, cases) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
      let (l1, e1) = l1e1 in
      let (caseList, n2) =
        let rec transform_lssc idx = function
        | [] -> ([], idx)
        | x :: rest ->
          let (c1, n3) = transform_ssc0 idx x in
          let (rest', n4) = transform_lssc n3 rest in ((c1 :: rest'), n4)
        in transform_lssc n1 cases
      in
      ((app l1 ((MkStatement (tags0, (StatSwitch (e1, caseList)),
         typ)) :: [])), n2)
    | StatVariable (typ', name, init) ->
      (match init with
       | Some expr ->
         let (l1e1, n1) = transform_Expr_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatVariable (typ', name, (Some
            e1))), typ)) :: [])), n1)
       | None -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx))
    | _ -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
  and transform_stmt0 nameIdx = function
  | MkStatement (tags0, stmt0, typ) ->
    transform_stmtpt0 nameIdx tags0 stmt0 typ
  and transform_blk0 nameIdx = function
  | BlockEmpty tag -> ((BlockEmpty tag), nameIdx)
  | BlockCons (stmt, blk') ->
    let (stl1, n1) = transform_stmt0 nameIdx stmt in
    let (blk2, n2) = transform_blk0 n1 blk' in
    ((prepend_to_block stl1 blk2), n2)
  and transform_ssc0 nameIdx ssc = match ssc with
  | StatSwCaseAction (tags0, label, code) ->
    let (blk, n1) = transform_blk0 nameIdx code in
    ((StatSwCaseAction (tags0, label, blk)), n1)
  | StatSwCaseFallThrough (_, _) -> (ssc, nameIdx)
  in transform_stmt0

(** val transform_blk :
    'a1 -> Bigint.t -> 'a1 coq_Block -> 'a1 coq_Block * Bigint.t **)

let transform_blk default_tag =
  let rec transform_stmtpt0 nameIdx tags0 stmt typ =
    match stmt with
    | StatMethodCall (_, _, _) ->
      (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
    | StatAssignment (lhs, rhs) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx lhs in
      let (l1, e1) = l1e1 in
      let (l2e2, n2) = transform_Expr_stmt default_tag n1 rhs in
      let (l2, e2) = l2e2 in
      ((app l1
         (app l2 ((MkStatement (tags0, (StatAssignment (e1, e2)),
           typ)) :: []))), n2)
    | StatDirectApplication (typ', args) ->
      let (l1e1, n1) = transform_list_stmt default_tag nameIdx args in
      let (l1, e1) = l1e1 in
      ((app l1 ((MkStatement (tags0, (StatDirectApplication (typ', e1)),
         typ)) :: [])), n1)
    | StatConditional (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx cond in
      let (l1, _) = l1e1 in
      let (stl2, n2) = transform_stmt0 n1 tru in
      let (stl3, n3) =
        match fls with
        | Some stmt' -> transform_stmt0 n2 stmt'
        | None -> ([], n2)
      in
      ((app l1 (app stl2 stl3)), n3)
    | StatBlock block ->
      let (blk, n1) = transform_blk0 nameIdx block in
      (((MkStatement (tags0, (StatBlock blk), typ)) :: []), n1)
    | StatExit -> (((MkStatement (tags0, StatExit, typ)) :: []), nameIdx)
    | StatEmpty -> (((MkStatement (tags0, StatEmpty, typ)) :: []), nameIdx)
    | StatReturn expr0 ->
      (match expr0 with
       | Some expr ->
         let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatReturn (Some e1)), typ)) :: [])),
         n1)
       | None ->
         (((MkStatement (tags0, (StatReturn None), typ)) :: []), nameIdx))
    | StatSwitch (expr, cases) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
      let (l1, e1) = l1e1 in
      let (caseList, n2) =
        let rec transform_lssc idx = function
        | [] -> ([], idx)
        | x :: rest ->
          let (c1, n3) = transform_ssc0 idx x in
          let (rest', n4) = transform_lssc n3 rest in ((c1 :: rest'), n4)
        in transform_lssc n1 cases
      in
      ((app l1 ((MkStatement (tags0, (StatSwitch (e1, caseList)),
         typ)) :: [])), n2)
    | StatVariable (typ', name, init) ->
      (match init with
       | Some expr ->
         let (l1e1, n1) = transform_Expr_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatVariable (typ', name, (Some
            e1))), typ)) :: [])), n1)
       | None -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx))
    | _ -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
  and transform_stmt0 nameIdx = function
  | MkStatement (tags0, stmt0, typ) ->
    transform_stmtpt0 nameIdx tags0 stmt0 typ
  and transform_blk0 nameIdx = function
  | BlockEmpty tag -> ((BlockEmpty tag), nameIdx)
  | BlockCons (stmt, blk') ->
    let (stl1, n1) = transform_stmt0 nameIdx stmt in
    let (blk2, n2) = transform_blk0 n1 blk' in
    ((prepend_to_block stl1 blk2), n2)
  and transform_ssc0 nameIdx ssc = match ssc with
  | StatSwCaseAction (tags0, label, code) ->
    let (blk, n1) = transform_blk0 nameIdx code in
    ((StatSwCaseAction (tags0, label, blk)), n1)
  | StatSwCaseFallThrough (_, _) -> (ssc, nameIdx)
  in transform_blk0

(** val transform_ssc :
    'a1 -> Bigint.t -> 'a1 coq_StatementSwitchCase -> 'a1
    coq_StatementSwitchCase * Bigint.t **)

let transform_ssc default_tag =
  let rec transform_stmtpt0 nameIdx tags0 stmt typ =
    match stmt with
    | StatMethodCall (_, _, _) ->
      (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
    | StatAssignment (lhs, rhs) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx lhs in
      let (l1, e1) = l1e1 in
      let (l2e2, n2) = transform_Expr_stmt default_tag n1 rhs in
      let (l2, e2) = l2e2 in
      ((app l1
         (app l2 ((MkStatement (tags0, (StatAssignment (e1, e2)),
           typ)) :: []))), n2)
    | StatDirectApplication (typ', args) ->
      let (l1e1, n1) = transform_list_stmt default_tag nameIdx args in
      let (l1, e1) = l1e1 in
      ((app l1 ((MkStatement (tags0, (StatDirectApplication (typ', e1)),
         typ)) :: [])), n1)
    | StatConditional (cond, tru, fls) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx cond in
      let (l1, _) = l1e1 in
      let (stl2, n2) = transform_stmt0 n1 tru in
      let (stl3, n3) =
        match fls with
        | Some stmt' -> transform_stmt0 n2 stmt'
        | None -> ([], n2)
      in
      ((app l1 (app stl2 stl3)), n3)
    | StatBlock block ->
      let (blk, n1) = transform_blk0 nameIdx block in
      (((MkStatement (tags0, (StatBlock blk), typ)) :: []), n1)
    | StatExit -> (((MkStatement (tags0, StatExit, typ)) :: []), nameIdx)
    | StatEmpty -> (((MkStatement (tags0, StatEmpty, typ)) :: []), nameIdx)
    | StatReturn expr0 ->
      (match expr0 with
       | Some expr ->
         let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatReturn (Some e1)), typ)) :: [])),
         n1)
       | None ->
         (((MkStatement (tags0, (StatReturn None), typ)) :: []), nameIdx))
    | StatSwitch (expr, cases) ->
      let (l1e1, n1) = transform_exp_stmt default_tag nameIdx expr in
      let (l1, e1) = l1e1 in
      let (caseList, n2) =
        let rec transform_lssc idx = function
        | [] -> ([], idx)
        | x :: rest ->
          let (c1, n3) = transform_ssc0 idx x in
          let (rest', n4) = transform_lssc n3 rest in ((c1 :: rest'), n4)
        in transform_lssc n1 cases
      in
      ((app l1 ((MkStatement (tags0, (StatSwitch (e1, caseList)),
         typ)) :: [])), n2)
    | StatVariable (typ', name, init) ->
      (match init with
       | Some expr ->
         let (l1e1, n1) = transform_Expr_stmt default_tag nameIdx expr in
         let (l1, e1) = l1e1 in
         ((app l1 ((MkStatement (tags0, (StatVariable (typ', name, (Some
            e1))), typ)) :: [])), n1)
       | None -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx))
    | _ -> (((MkStatement (tags0, stmt, typ)) :: []), nameIdx)
  and transform_stmt0 nameIdx = function
  | MkStatement (tags0, stmt0, typ) ->
    transform_stmtpt0 nameIdx tags0 stmt0 typ
  and transform_blk0 nameIdx = function
  | BlockEmpty tag -> ((BlockEmpty tag), nameIdx)
  | BlockCons (stmt, blk') ->
    let (stl1, n1) = transform_stmt0 nameIdx stmt in
    let (blk2, n2) = transform_blk0 n1 blk' in
    ((prepend_to_block stl1 blk2), n2)
  and transform_ssc0 nameIdx ssc = match ssc with
  | StatSwCaseAction (tags0, label, code) ->
    let (blk, n1) = transform_blk0 nameIdx code in
    ((StatSwCaseAction (tags0, label, blk)), n1)
  | StatSwCaseFallThrough (_, _) -> (ssc, nameIdx)
  in transform_ssc0

(** val expr_to_decl :
    'a1 -> ('a1 t * 'a1 coq_Expression) -> 'a1 coq_Declaration **)

let expr_to_decl default_tag = function
| (name, e) ->
  let MkExpression (tags0, expr, typ, dir) = e in
  (match expr with
   | ExpNamelessInstantiation (typ', args) ->
     DeclInstantiation (tags0, typ', args, name, None)
   | _ ->
     DeclVariable (default_tag, typ, name, (Some (MkExpression (tags0, expr,
       typ, dir)))))

(** val transform_list' :
    (Bigint.t -> 'a1 -> 'a1 list * Bigint.t) -> Bigint.t -> 'a1 list -> 'a1
    list * Bigint.t **)

let rec transform_list' f nameIdx = function
| [] -> ([], nameIdx)
| x :: rest ->
  let (l1, n1) = f nameIdx x in
  let (l2, n2) = transform_list' f n1 rest in ((app l1 l2), n2)

(** val transform_match :
    'a1 -> Bigint.t -> 'a1 coq_Match -> ('a1 coq_Declaration list * 'a1
    coq_Match) * Bigint.t **)

let transform_match default_tag nameIdx mt = match mt with
| MkMatch (tags0, expr, typ) ->
  (match expr with
   | MatchDontCare -> (([], mt), nameIdx)
   | MatchExpression exp ->
     let (l1e1, n1) = transform_exp default_tag nameIdx exp in
     let (l1, e1) = l1e1 in
     (((map (expr_to_decl default_tag) l1), (MkMatch (tags0, (MatchExpression
     e1), typ))), n1))

(** val transform_psrcase :
    'a1 -> Bigint.t -> 'a1 coq_ParserCase -> ('a1 coq_Declaration list * 'a1
    coq_ParserCase) * Bigint.t **)

let transform_psrcase default_tag nameIdx = function
| MkParserCase (tags0, matches, next) ->
  let (l1m1, n1) =
    transform_list (transform_match default_tag) nameIdx matches
  in
  let (l1, m1) = l1m1 in ((l1, (MkParserCase (tags0, m1, next))), n1)

(** val transform_psrtrans :
    'a1 -> Bigint.t -> 'a1 coq_ParserTransition -> ('a1 coq_Declaration
    list * 'a1 coq_ParserTransition) * Bigint.t **)

let transform_psrtrans default_tag nameIdx pt = match pt with
| ParserDirect (_, _) -> (([], pt), nameIdx)
| ParserSelect (tags0, exprs, cases) ->
  let (l1e1, n1) = transform_exprs default_tag nameIdx exprs in
  let (l1, e1) = l1e1 in
  let (l2c2, n2) = transform_list (transform_psrcase default_tag) n1 cases in
  let (l2, c2) = l2c2 in
  (((app (map (expr_to_decl default_tag) l1) l2), (ParserSelect (tags0, e1,
  c2))), n2)

(** val transform_psrst :
    'a1 -> Bigint.t -> 'a1 coq_ParserState -> ('a1 coq_Declaration list * 'a1
    coq_ParserState) * Bigint.t **)

let transform_psrst default_tag nameIdx = function
| MkParserState (tags0, name, statements, transition) ->
  let (l1, n1) =
    transform_list' (transform_stmt default_tag) nameIdx statements
  in
  let (l2t2, n2) = transform_psrtrans default_tag n1 transition in
  let (l2, t2) = l2t2 in ((l2, (MkParserState (tags0, name, l1, t2))), n2)

(** val transform_tblkey :
    'a1 -> Bigint.t -> 'a1 coq_TableKey -> ('a1 coq_Declaration list * 'a1
    coq_TableKey) * Bigint.t **)

let transform_tblkey default_tag nameIdx = function
| MkTableKey (tags0, key, match_kind) ->
  let (l1e1, n1) = transform_exp default_tag nameIdx key in
  let (l1, e1) = l1e1 in
  (((map (expr_to_decl default_tag) l1), (MkTableKey (tags0, e1,
  match_kind))), n1)

(** val transform_opt :
    'a1 -> Bigint.t -> 'a1 coq_Expression option -> (('a1 t * 'a1
    coq_Expression) list * 'a1 coq_Expression option) * Bigint.t **)

let transform_opt default_tag nameIdx = function
| Some exp ->
  let (l1e1, n1) = transform_exp default_tag nameIdx exp in
  let (l1, e1) = l1e1 in ((l1, (Some e1)), n1)
| None -> (([], None), nameIdx)

(** val transform_tpar :
    'a1 -> Bigint.t -> 'a1 coq_TablePreActionRef -> ('a1 coq_Declaration
    list * 'a1 coq_TablePreActionRef) * Bigint.t **)

let transform_tpar default_tag nameIdx = function
| MkTablePreActionRef (name, args) ->
  let (l1e1, n1) = transform_list (transform_opt default_tag) nameIdx args in
  let (l1, e1) = l1e1 in
  (((map (expr_to_decl default_tag) l1), (MkTablePreActionRef (name, e1))),
  n1)

(** val transform_tar :
    'a1 -> Bigint.t -> 'a1 coq_TableActionRef -> ('a1 coq_Declaration
    list * 'a1 coq_TableActionRef) * Bigint.t **)

let transform_tar default_tag nameIdx = function
| MkTableActionRef (tags0, action, typ) ->
  let (l1e1, n1) = transform_tpar default_tag nameIdx action in
  let (l1, e1) = l1e1 in ((l1, (MkTableActionRef (tags0, e1, typ))), n1)

(** val transform_tblenty :
    'a1 -> Bigint.t -> 'a1 coq_TableEntry -> ('a1 coq_Declaration list * 'a1
    coq_TableEntry) * Bigint.t **)

let transform_tblenty default_tag nameIdx = function
| MkTableEntry (tags0, matches, action) ->
  let (l1e1, n1) =
    transform_list (transform_match default_tag) nameIdx matches
  in
  let (l1, e1) = l1e1 in
  let (l2e2, n2) = transform_tar default_tag n1 action in
  let (l2, e2) = l2e2 in (((app l1 l2), (MkTableEntry (tags0, e1, e2))), n2)

(** val transform_tblprop :
    'a1 -> Bigint.t -> 'a1 coq_TableProperty -> ('a1 coq_Declaration
    list * 'a1 coq_TableProperty) * Bigint.t **)

let transform_tblprop default_tag nameIdx = function
| MkTableProperty (tags0, const, name, value) ->
  let (l1e1, n1) = transform_exp default_tag nameIdx value in
  let (l1, e1) = l1e1 in
  (((map (expr_to_decl default_tag) l1), (MkTableProperty (tags0, const,
  name, e1))), n1)

(** val transform_membr :
    'a1 -> Bigint.t -> ('a1 t * 'a1 coq_Expression) -> ('a1 coq_Declaration
    list * ('a1 t * 'a1 coq_Expression)) * Bigint.t **)

let transform_membr default_tag nameIdx = function
| (n, exp) ->
  let (l1e1, n1) = transform_exp default_tag nameIdx exp in
  let (l1, e1) = l1e1 in (((map (expr_to_decl default_tag) l1), (n, e1)), n1)

(** val lastDecl : 'a1 -> 'a1 coq_Declaration list -> 'a1 coq_Declaration **)

let lastDecl default_tag l =
  last l (DeclError (default_tag, []))

(** val transform_decl :
    'a1 -> Bigint.t -> 'a1 coq_Declaration -> 'a1 coq_Declaration
    list * Bigint.t **)

let rec transform_decl default_tag nameIdx decl = match decl with
| DeclParser (tags0, name, type_params, params, cparams, locals, states) ->
  let (local', n1) =
    let rec transform_decl_list idx = function
    | [] -> ([], idx)
    | x :: rest ->
      let (l2, n2) = transform_decl default_tag idx x in
      let (l3, n3) = transform_decl_list n2 rest in ((app l2 l3), n3)
    in transform_decl_list nameIdx locals
  in
  let (l2s2, _) = transform_list (transform_psrst default_tag) n1 states in
  let (l2, s2) = l2s2 in
  ((app local'
     (app l2 ((DeclParser (tags0, name, type_params, params, cparams, local',
       s2)) :: []))), n1)
| DeclControl (tags0, name, type_params, params, cparams, locals, appl) ->
  let (local', n1) =
    let rec transform_decl_list idx = function
    | [] -> ([], idx)
    | x :: rest ->
      let (l2, n2) = transform_decl default_tag idx x in
      let (l3, n3) = transform_decl_list n2 rest in ((app l2 l3), n3)
    in transform_decl_list nameIdx locals
  in
  let (blk, n2) = transform_blk default_tag n1 appl in
  (((DeclControl (tags0, name, type_params, params, cparams, local',
  blk)) :: []), n2)
| DeclFunction (tags0, ret, name, type_params, params, body) ->
  let (blk, n1) = transform_blk default_tag nameIdx body in
  (((DeclFunction (tags0, ret, name, type_params, params, blk)) :: []), n1)
| DeclVariable (tags0, typ, name, init) ->
  (match init with
   | Some expr ->
     let (l1e1, n1) = transform_Expr default_tag nameIdx expr in
     let (l1, e1) = l1e1 in
     ((app (map (expr_to_decl default_tag) l1) ((DeclVariable (tags0, typ,
        name, (Some e1))) :: [])), n1)
   | None -> ((decl :: []), nameIdx))
| DeclValueSet (tags0, typ, size, name) ->
  let (l1e1, n1) = transform_Expr default_tag nameIdx size in
  let (l1, e1) = l1e1 in
  ((app (map (expr_to_decl default_tag) l1) ((DeclValueSet (tags0, typ, e1,
     name)) :: [])), n1)
| DeclAction (tags0, name, data_params, ctrl_params, body) ->
  let (blk, n1) = transform_blk default_tag nameIdx body in
  (((DeclAction (tags0, name, data_params, ctrl_params, blk)) :: []), n1)
| DeclTable (tags0, name, key, actions, entries, default_action, size,
             custom_properties) ->
  let (l1e1, n1) = transform_list (transform_tblkey default_tag) nameIdx key
  in
  let (l1, e1) = l1e1 in
  let (l2e2, n2) = transform_list (transform_tar default_tag) n1 actions in
  let (l2, e2) = l2e2 in
  (match entries with
   | Some ets ->
     let (l4e4, n4) = transform_list (transform_tblenty default_tag) n2 ets in
     let (l4, e4) = l4e4 in
     let l3e3 = (l4, (Some e4)) in
     let (l3, e3) = l3e3 in
     (match default_action with
      | Some da ->
        let (l6e6, n6) = transform_tar default_tag n4 da in
        let (l6, e6) = l6e6 in
        let l5e5 = (l6, (Some e6)) in
        let (l5, e5) = l5e5 in
        let (l6e7, n7) =
          transform_list (transform_tblprop default_tag) n6 custom_properties
        in
        let (l7, e7) = l6e7 in
        ((app l1
           (app l2
             (app l3
               (app l5
                 (app l7 ((DeclTable (tags0, name, e1, e2, e3, e5, size,
                   e7)) :: [])))))), n7)
      | None ->
        let l5e5 = ([], None) in
        let (l5, e5) = l5e5 in
        let (l6e6, n6) =
          transform_list (transform_tblprop default_tag) n4 custom_properties
        in
        let (l6, e6) = l6e6 in
        ((app l1
           (app l2
             (app l3
               (app l5
                 (app l6 ((DeclTable (tags0, name, e1, e2, e3, e5, size,
                   e6)) :: [])))))), n6))
   | None ->
     let l3e3 = ([], None) in
     let (l3, e3) = l3e3 in
     (match default_action with
      | Some da ->
        let (l6e6, n6) = transform_tar default_tag n2 da in
        let (l6, e6) = l6e6 in
        let l5e5 = (l6, (Some e6)) in
        let (l5, e5) = l5e5 in
        let (l6e7, n7) =
          transform_list (transform_tblprop default_tag) n6 custom_properties
        in
        let (l7, e7) = l6e7 in
        ((app l1
           (app l2
             (app l3
               (app l5
                 (app l7 ((DeclTable (tags0, name, e1, e2, e3, e5, size,
                   e7)) :: [])))))), n7)
      | None ->
        let l5e5 = ([], None) in
        let (l5, e5) = l5e5 in
        let (l6e6, n6) =
          transform_list (transform_tblprop default_tag) n2 custom_properties
        in
        let (l6, e6) = l6e6 in
        ((app l1
           (app l2
             (app l3
               (app l5
                 (app l6 ((DeclTable (tags0, name, e1, e2, e3, e5, size,
                   e6)) :: [])))))), n6)))
| DeclSerializableEnum (tags0, typ, name, members) ->
  let (l1e1, n1) =
    transform_list (transform_membr default_tag) nameIdx members
  in
  let (l1, e1) = l1e1 in
  ((app l1 ((DeclSerializableEnum (tags0, typ, name, e1)) :: [])), n1)
| DeclTypeDef (tags0, name, typ_or_decl) ->
  (match typ_or_decl with
   | Coq_inl _ -> ((decl :: []), nameIdx)
   | Coq_inr decl' ->
     let (l1, n1) = transform_decl default_tag nameIdx decl' in
     ((app (removelast l1) ((DeclTypeDef (tags0, name, (Coq_inr
        (lastDecl default_tag l1)))) :: [])), n1))
| DeclNewType (tags0, name, typ_or_decl) ->
  (match typ_or_decl with
   | Coq_inl _ -> ((decl :: []), nameIdx)
   | Coq_inr decl' ->
     let (l1, n1) = transform_decl default_tag nameIdx decl' in
     ((app (removelast l1) ((DeclNewType (tags0, name, (Coq_inr
        (lastDecl default_tag l1)))) :: [])), n1))
| _ -> ((decl :: []), nameIdx)

(** val transform_prog : 'a1 -> 'a1 program -> 'a1 program **)

let transform_prog default_tag prog =
  let (l', _) =
    transform_list' (transform_decl default_tag)
      (Bigint.of_zarith_bigint Z.zero) prog
  in
  l'
