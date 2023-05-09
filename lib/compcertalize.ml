(* The main reason for this file is that compcert extracts its coq codes not using bigint *)
(* Therefore, we currently have two separate AST for p4cub, one uses bigint, the other uses coq_n etc*)
open Poulet4_Ccomp.Camlcoq
open Poulet4_Ccomp.AST0
module Prev = Poulet4.AST
let rec string_charlist (s:String.t) = 
    let l = String.length s in 
    if(l = 0) then []
    else s.[0] :: string_charlist (String.sub s 1 (l-1))
   
let bigint_positive i = P.of_int64 (Int64.of_string (Bignum.to_string_accurate (Bignum.of_bigint i)))
let bigint_coqN i = N.of_int64 (Int64.of_string (Bignum.to_string_accurate (Bignum.of_bigint i)))
let bigint_coqZ i = Z.of_sint64 (Int64.of_string (Bignum.to_string_accurate (Bignum.of_bigint i)))
let convert_paramarg (x : ('a, 'b) Prev.paramarg) = 
    match x with 
    | Prev.PAIn a -> PAIn a
    | Prev.PAOut b -> PAOut b 
    | Prev.PAInOut b -> PAInOut b

let convert_paramarg_poly (x : ('a,'b) Prev.paramarg) (funa: 'a -> 'c)
    (funb : 'b -> 'd) = 
    match x with 
    | Prev.PAIn a -> PAIn (funa a)
    | Prev.PAOut b -> PAOut (funb b) 
    | Prev.PAInOut b -> PAInOut (funb b)

let sum_convert_poly (x: ('a,'b) Poulet4.Datatypes.sum)
    (funa : 'a -> 'c) (funb : 'b -> 'd) =
    match x with 
    | Poulet4.Datatypes.Coq_inl a -> 
        Poulet4_Ccomp.Datatypes.Coq_inl (funa a)
    | Poulet4.Datatypes.Coq_inr b -> 
        Poulet4_Ccomp.Datatypes.Coq_inr (funb b)

let convert_Field_poly (x: 'k * 'v) (funk : 'k -> 'k1)
(funv : 'v -> 'v1): 'k1 * 'v1 =
    (funk (fst x), funv (snd x))

let convert_Fields_poly (x: ('k * 'v) list) (funk : 'k -> 'k1)
(funv : 'v -> 'v1): ('k1 * 'v1) list  =
    List.map (fun x -> convert_Field_poly x funk funv) x

let convert_arrow_poly (x : ('k,'a,'b) Prev.arrow)
    (funk : 'k -> 'k1)
    (funa : 'a -> 'a1)
    (funb : 'b -> 'b1)
    : ('k1,'a1,'b1) arrow = 
    {
        paramargs = 
            List.map 
            (fun y -> (funk (fst y), convert_paramarg_poly (snd y) funa funb)) 
            x.paramargs;
        rtrns = Option.map funb x.rtrns;
    }


let rec convert_type (x : Prev.Typ.t) =
    match x with 
    | Prev.Typ.Bool -> Typ.Bool
    | Prev.Typ.Bit i -> Typ.Bit (bigint_coqN i)
    | Prev.Typ.Int i -> Typ.Int (bigint_positive i)
    | Prev.Typ.Error -> Typ.Error
    | Prev.Typ.Struct (b,fs) -> Typ.Struct (b, List.map convert_type fs)
    | Prev.Typ.Array (i, t) -> Typ.Array (bigint_coqN i, convert_type t)
    | Prev.Typ.Var s -> Typ.Var (Nat.of_int s)
    | Prev.Typ.VarBit z -> Typ.VarBit (bigint_coqN z)


let convert_params (fs) = 
    convert_Fields_poly fs 
    string_charlist
    (fun x -> convert_paramarg_poly x convert_type convert_type)

let convert_arrowT (a) = 
    convert_arrow_poly a string_charlist convert_type convert_type

let convert_cnstr : Prev.Cnstr.t -> Cnstr.t =
  function
  | Prev.Cnstr.Control -> Cnstr.Control
  | Prev.Cnstr.Parser  -> Cnstr.Parser

let convert_it : Prev.InstTyp.t -> InstTyp.t =
    function
    | Prev.InstTyp.Ctr (f,b,c) -> InstTyp.Ctr (
        convert_cnstr f,
        List.map string_charlist b,
        convert_params c
    )
    | Prev.InstTyp.Package -> InstTyp.Package
    | Prev.InstTyp.Extern s -> InstTyp.Extern (string_charlist s)

let convert_constructor_params =
  List.map (fun (x,it) -> string_charlist x, convert_it it)

let convert_una (u:Prev.Una.t) =
    match u with
    | Prev.Una.Not -> Una.Not
    | Prev.Una.BitNot -> Una.BitNot 
    | Prev.Una.Minus -> Una.Minus
    | Prev.Una.IsValid -> Una.IsValid

let convert_bin (b: Prev.Bin.t) = 
    match b with
    | Prev.Bin.Plus -> Bin.Plus
    | Prev.Bin.PlusSat -> Bin.PlusSat
    | Prev.Bin.Minus -> Bin.Minus
    | Prev.Bin.MinusSat -> Bin.MinusSat  
    | Prev.Bin.Times -> Bin.Times 
    | Prev.Bin.Shl -> Bin.Shl 
    | Prev.Bin.Shr -> Bin.Shr 
    | Prev.Bin.Le -> Bin.Le
    | Prev.Bin.Ge -> Bin.Ge
    | Prev.Bin.Lt -> Bin.Lt 
    | Prev.Bin.Gt -> Bin.Gt
    | Prev.Bin.Eq -> Bin.Eq
    | Prev.Bin.NotEq -> Bin.NotEq 
    | Prev.Bin.BitAnd -> Bin.BitAnd 
    | Prev.Bin.BitXor -> Bin.BitXor
    | Prev.Bin.BitOr -> Bin.BitOr 
    | Prev.Bin.PlusPlus -> Bin.PlusPlus
    | Prev.Bin.And -> Bin.And
    | Prev.Bin.Or -> Bin.Or

let convert_Lst : Prev.Lst.t -> Lst.t =
function
| Prev.Lst.Struct -> Lst.Struct
| Prev.Lst.Header b -> Lst.Header b
| Prev.Lst.Array t -> Lst.Array (convert_type t)

let rec convert_expression (x : Prev.Exp.t) = match x with
    | Prev.Exp.Bool (b) -> Exp.Bool (b)
    | Prev.Exp.Bit (w,v) -> 
        Exp.Bit (bigint_coqN w,bigint_coqZ v)
    | Prev.Exp.Int (w,v) -> 
        Exp.Int (bigint_positive w,bigint_coqZ v)
    | Prev.Exp.VarBit (mw, w, z) ->
        Exp.VarBit (bigint_coqN mw, bigint_coqN w, bigint_coqZ z)
    | Prev.Exp.Var (t,x,n) ->
        Exp.Var (convert_type t, string_charlist x, Nat.of_int n)
    | Prev.Exp.Slice (a, b, e) ->
        Exp.Slice (bigint_positive a, bigint_positive b,convert_expression e)
    | Prev.Exp.Cast (t, e)->
        Exp.Cast (convert_type t, 
        convert_expression e)
    | Prev.Exp.Uop (t,u,e) ->
        Exp.Uop (convert_type t, convert_una u,
        convert_expression e)
    | Prev.Exp.Bop (t,b,e,f) ->
        Exp.Bop (convert_type t, convert_bin b,
        convert_expression e,
        convert_expression f)
    | Prev.Exp.Lists (ls,es) ->
        Exp.Lists (convert_Lst ls, List.map convert_expression es)
    | Prev.Exp.Member (t,n,e) ->
        Exp.Member(convert_type t, Nat.of_int n,
        convert_expression e)
    | Prev.Exp.Error (s) ->
        Exp.Error (string_charlist s)
    | Prev.Exp.Index (t, e1, e2) -> 
        Exp.Index (convert_type t, convert_expression e1, convert_expression e2)


let args_convert : Prev.Exp.args -> Exp.args =
   List.map
   (fun x -> convert_paramarg_poly x convert_expression convert_expression)

let constructor_args_convert
  : Prev.Top.constructor_args -> Top.constructor_args =
    List.map string_charlist

let state_label_convert (s: Prev.Lbl.t) : Lbl.t = 
    match s with 
    | Prev.Lbl.Start ->Lbl.Start
    | Prev.Lbl.Accept ->Lbl.Accept 
    | Prev.Lbl.Reject ->Lbl.Reject 
    | Prev.Lbl.Name s ->Lbl.Name (Nat.of_int s)

let rec pat_convert (p: Prev.Pat.t) : Pat.t = 
    match p with 
    | Prev.Pat.Wild ->  Pat.Wild
    | Prev.Pat.Mask (p,q) -> Pat.Mask (pat_convert p, pat_convert q)
    | Prev.Pat.Range (p,q) -> Pat.Range (pat_convert p, pat_convert q)
    | Prev.Pat.Bit (i,j) -> Pat.Bit (bigint_coqN i, bigint_coqZ j)
    | Prev.Pat.Int (i,j) -> Pat.Int (bigint_positive i, bigint_coqZ j)
    | Prev.Pat.Lists l -> Pat.Lists (List.map pat_convert l)

let convert_trns (e :  Prev.Trns.t) =
    match e with 
    | Prev.Trns.Direct s -> 
        Trns.Direct (state_label_convert s)
    | Prev.Trns.Select (e,st,fs) ->
        Trns.Select(convert_expression e, 
        state_label_convert st,
        convert_Fields_poly fs pat_convert state_label_convert)

let convert_call : Prev.Call.t -> Call.t =
function
| Prev.Call.Funct (f,ts,e) ->
  Call.Funct (string_charlist f, List.map convert_type ts, Option.map convert_expression e)
| Prev.Call.Action (a,es) ->
  Call.Action (string_charlist a, List.map convert_expression es)
| Prev.Call.Method (x,m,ts,e) ->
  Call.Method (string_charlist x,string_charlist m,
  List.map convert_type ts,Option.map convert_expression e)
| Prev.Call.Inst (x,es) -> Call.Inst (string_charlist x, List.map string_charlist es)

let rec stm_convert (s:  Prev.Stm.t) = 
    match s with
    | Prev.Stm.Trans tr -> Stm.Trans (convert_trns tr)
    | Prev.Stm.App (fk,es) -> Stm.App (convert_call fk,args_convert es)
    | Prev.Stm.Skip -> Stm.Skip
    | Prev.Stm.LetIn (x, e, s) -> 
        Stm.LetIn (string_charlist x,
        sum_convert_poly e convert_type convert_expression,
        stm_convert s)
    | Prev.Stm.Asgn (x,y) ->
        Stm.Asgn (convert_expression x,
        convert_expression y)
    | Prev.Stm.SetValidity (b,e) ->
        Stm.SetValidity (b, convert_expression e)
    | Prev.Stm.Cond (e,x,y) ->
        Stm.Cond (convert_expression e,
        stm_convert x, stm_convert y)
    | Prev.Stm.Seq (x,y) ->
        Stm.Seq (stm_convert x,
        stm_convert y)
    | Prev.Stm.Ret e ->
        Stm.Ret (Option.map convert_expression e)
    | Prev.Stm.Exit -> Stm.Exit
    | Prev.Stm.Invoke (eo,t) ->
        Stm.Invoke (Option.map convert_expression eo, string_charlist t)

let controld_convert (d :  Prev.Ctrl.t) = 
    match d with 
    | Prev.Ctrl.Var (x,e) ->
        Ctrl.Var
         (string_charlist x,
          sum_convert_poly e convert_type convert_expression)
    | Prev.Ctrl.Action (a, ctrl_params, data_params, st) ->
        Ctrl.Action (
            string_charlist a,
            List.map (fun (x,t) -> string_charlist x, convert_type t) ctrl_params,
            convert_params data_params,
            stm_convert st)
    | Prev.Ctrl.Table (t, key, mks, def) ->
        Ctrl.Table (
            string_charlist t,
            List.map (fun (e,mk) -> convert_expression e, string_charlist mk) key,
            List.map (fun (a,args) -> string_charlist a, args_convert args) mks,
            Option.map (fun (a, es) -> string_charlist a, List.map convert_expression es) def)

let topdecl_convert (d:  Prev.Top.t) =
    match d with
    | Prev.Top.Instantiate (n,m,l,c,es) ->
        Top.Instantiate (
            string_charlist n,
            string_charlist m, 
            List.map convert_type l,
            constructor_args_convert c,
            List.map convert_expression es)
    | Prev.Top.Extern (e, n, c, eps, fs) ->
        Top.Extern (
            string_charlist e,
            Nat.of_int n,
            convert_constructor_params c,
            List.map convert_type eps,
            convert_Fields_poly fs string_charlist
            (fun ((ts,exs),arr) ->
             (Nat.of_int ts, List.map string_charlist exs), convert_arrowT arr))
    | Prev.Top.Control (s, c, ts, fs, p, d, st) ->
        Top.Control (
            string_charlist s,
            convert_constructor_params c,
            List.map convert_type ts,
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            List.map controld_convert d,
            stm_convert st)
    | Prev.Top.Parser (s, c, ts, fs, p, bl, fs2) ->
        Top.Parser (
            string_charlist s, 
            convert_constructor_params c,
            List.map convert_type ts,
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            stm_convert bl,
            List.map stm_convert fs2)
    | Prev.Top.Funct (n, l, a, st) ->
        Top.Funct (
            string_charlist n,
            Nat.of_int l, 
            convert_arrowT a,
            stm_convert st)
