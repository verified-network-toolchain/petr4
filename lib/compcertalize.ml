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


let rec convert_type (x : Prev.Expr.t) =
    match x with 
    | Prev.Expr.TBool -> Expr.TBool
    | Prev.Expr.TBit i -> Expr.TBit (bigint_coqN i)
    | Prev.Expr.TInt i -> Expr.TInt (bigint_positive i)
    | Prev.Expr.TError -> Expr.TError
    | Prev.Expr.TStruct (b,fs) -> Expr.TStruct (b, List.map convert_type fs)
    | Prev.Expr.TArray (i, t) -> Expr.TArray (bigint_coqN i, convert_type t)
    | Prev.Expr.TVar s -> Expr.TVar (Nat.of_int s)
    | Prev.Expr.TVarBit z -> Expr.TVarBit (bigint_coqN z)


let convert_params (fs) = 
    convert_Fields_poly fs 
    string_charlist
    (fun x -> convert_paramarg_poly x convert_type convert_type)

let convert_arrowT (a) = 
    convert_arrow_poly a string_charlist convert_type convert_type


let convert_it : Prev.TopDecl.it -> TopDecl.it =
    function
    | Prev.TopDecl.ControlInstType (b,c) -> TopDecl.ControlInstType (
        List.map string_charlist b,
        convert_params c
    )
    | Prev.TopDecl.ParserInstType (b,c) -> TopDecl.ParserInstType (
        List.map string_charlist b,
        convert_params c
    )
    | Prev.TopDecl.PackageInstType -> TopDecl.PackageInstType
    | Prev.TopDecl.ExternInstType s -> TopDecl.ExternInstType (string_charlist s)

let convert_constructor_params =
  List.map (fun (x,it) -> string_charlist x, convert_it it)

let convert_uop (u:Prev.Expr.uop) =
    match u with
    | Prev.Expr.Not -> Expr.Not
    | Prev.Expr.BitNot -> Expr.BitNot 
    | Prev.Expr.UMinus -> Expr.UMinus
    | Prev.Expr.IsValid -> Expr.IsValid
    | Prev.Expr.SetValidity b -> Expr.SetValidity b

let convert_bop (b: Prev.Expr.bop) = 
    match b with
    | Prev.Expr.Plus -> Expr.Plus
    | Prev.Expr.PlusSat -> Expr.PlusSat
    | Prev.Expr.Minus -> Expr.Minus
    | Prev.Expr.MinusSat -> Expr.MinusSat  
    | Prev.Expr.Times -> Expr.Times 
    | Prev.Expr.Shl -> Expr.Shl 
    | Prev.Expr.Shr -> Expr.Shr 
    | Prev.Expr.Le -> Expr.Le
    | Prev.Expr.Ge -> Expr.Ge
    | Prev.Expr.Lt -> Expr.Lt 
    | Prev.Expr.Gt -> Expr.Gt
    | Prev.Expr.Eq -> Expr.Eq
    | Prev.Expr.NotEq -> Expr.NotEq 
    | Prev.Expr.BitAnd -> Expr.BitAnd 
    | Prev.Expr.BitXor -> Expr.BitXor
    | Prev.Expr.BitOr -> Expr.BitOr 
    | Prev.Expr.PlusPlus -> Expr.PlusPlus
    | Prev.Expr.And -> Expr.And
    | Prev.Expr.Or -> Expr.Or

let convert_lists : Prev.Expr.lists -> Expr.lists =
function
| Prev.Expr.Coq_lists_struct -> Expr.Coq_lists_struct
| Prev.Expr.Coq_lists_header b -> Expr.Coq_lists_header b
| Prev.Expr.Coq_lists_array t -> Expr.Coq_lists_array (convert_type t)

let rec convert_expression (x : Prev.Expr.e) = match x with
    | Prev.Expr.Bool (b) -> Expr.Bool (b)
    | Prev.Expr.Bit (w,v) -> 
        Expr.Bit (bigint_coqN w,bigint_coqZ v)
    | Prev.Expr.Int (w,v) -> 
        Expr.Int (bigint_positive w,bigint_coqZ v)
    | Prev.Expr.VarBit (mw, w, z) ->
        Expr.VarBit (bigint_coqN mw, bigint_coqN w, bigint_coqZ z)
    | Prev.Expr.Var (t,x,n) ->
        Expr.Var (convert_type t, string_charlist x, Nat.of_int n)
    | Prev.Expr.Slice (a, b, e) ->
        Expr.Slice (bigint_positive a, bigint_positive b,convert_expression e)
    | Prev.Expr.Cast (t, e)->
        Expr.Cast (convert_type t, 
        convert_expression e)
    | Prev.Expr.Uop (t,u,e) ->
        Expr.Uop (convert_type t, convert_uop u,
        convert_expression e)
    | Prev.Expr.Bop (t,b,e,f) ->
        Expr.Bop (convert_type t, convert_bop b,
        convert_expression e,
        convert_expression f)
    | Prev.Expr.Lists (ls,es) ->
        Expr.Lists (convert_lists ls, List.map convert_expression es)
    | Prev.Expr.Member (t,n,e) ->
        Expr.Member(convert_type t, Nat.of_int n,
        convert_expression e)
    | Prev.Expr.Error (s) ->
        Expr.Error (string_charlist s)
    | Prev.Expr.Index (t, e1, e2) -> 
        Expr.Index (convert_type t, convert_expression e1, convert_expression e2)


let args_convert : Prev.Expr.args -> Expr.args =
   List.map
   (fun x -> convert_paramarg_poly x convert_expression convert_expression)

let constructor_args_convert
  : Prev.TopDecl.constructor_args -> TopDecl.constructor_args =
    List.map string_charlist

let state_label_convert (s: Prev.Parser.state_label) : Parser.state_label = 
    match s with 
    | Prev.Parser.Start ->Parser.Start
    | Prev.Parser.Accept ->Parser.Accept 
    | Prev.Parser.Reject ->Parser.Reject 
    | Prev.Parser.Name s ->Parser.Name (Nat.of_int s)

let rec pat_convert (p: Prev.Parser.pat) : Parser.pat = 
    match p with 
    | Prev.Parser.Wild ->  Parser.Wild
    | Prev.Parser.Mask (p,q) -> Parser.Mask (pat_convert p, pat_convert q)
    | Prev.Parser.Range (p,q) -> Parser.Range (pat_convert p, pat_convert q)
    | Prev.Parser.Bit (i,j) -> Parser.Bit (bigint_coqN i, bigint_coqZ j)
    | Prev.Parser.Int (i,j) -> Parser.Int (bigint_positive i, bigint_coqZ j)
    | Prev.Parser.Lists l -> Parser.Lists (List.map pat_convert l)

let convert_trns (e :  Prev.Parser.trns) =
    match e with 
    | Prev.Parser.Direct s -> 
        Parser.Direct (state_label_convert s)
    | Prev.Parser.Select (e,st,fs) ->
        Parser.Select(convert_expression e, 
        state_label_convert st,
        convert_Fields_poly fs pat_convert state_label_convert)

let convert_fun_kind : Prev.Stmt.fun_kind -> Stmt.fun_kind =
function
| Prev.Stmt.Funct (f,ts,e) ->
  Stmt.Funct (string_charlist f, List.map convert_type ts, Option.map convert_expression e)
| Prev.Stmt.Action (a,es) ->
  Stmt.Action (string_charlist a, List.map convert_expression es)
| Prev.Stmt.Method (x,m,ts,e) ->
  Stmt.Method (string_charlist x,string_charlist m,
  List.map convert_type ts,Option.map convert_expression e)

let rec stmt_convert (s:  Prev.Stmt.s) = 
    match s with
    | Prev.Stmt.Transition tr -> Stmt.Transition (convert_trns tr)
    | Prev.Stmt.Call (fk,es) -> Stmt.Call (convert_fun_kind fk,args_convert es)
    | Prev.Stmt.Skip -> Stmt.Skip
    | Prev.Stmt.Var (x, e, s) -> 
        Stmt.Var (string_charlist x,
        sum_convert_poly e convert_type convert_expression,
        stmt_convert s)
    | Prev.Stmt.Assign (x,y) ->
        Stmt.Assign (convert_expression x,
        convert_expression y)
    | Prev.Stmt.Conditional (e,x,y) ->
        Stmt.Conditional (convert_expression e,
        stmt_convert x, stmt_convert y)
    | Prev.Stmt.Seq (x,y) ->
        Stmt.Seq (stmt_convert x,
        stmt_convert y)
    | Prev.Stmt.Return e ->
        Stmt.Return (Option.map convert_expression e)
    | Prev.Stmt.Exit -> Stmt.Exit
    | Prev.Stmt.Invoke (eo,t) ->
        Stmt.Invoke (Option.map convert_expression eo, string_charlist t)
    | Prev.Stmt.Apply (s, fs, a) ->
        Stmt.Apply (string_charlist s,
        List.map string_charlist fs,
        args_convert a)

let controld_convert (d :  Prev.Control.d) = 
    match d with 
    | Prev.Control.Var (x,e) ->
        Control.Var
         (string_charlist x,
          sum_convert_poly e convert_type convert_expression)
    | Prev.Control.Action (a, ctrl_params, data_params, st) ->
        Control.Action (
            string_charlist a,
            List.map (fun (x,t) -> string_charlist x, convert_type t) ctrl_params,
            convert_params data_params,
            stmt_convert st)
    | Prev.Control.Table (t, key, mks) ->
        Control.Table (
            string_charlist t,
            List.map (fun (e,mk) -> convert_expression e, string_charlist mk) key,
            List.map (fun (a,args) -> string_charlist a, args_convert args) mks)

let topdecl_convert (d:  Prev.TopDecl.d) =
    match d with
    | Prev.TopDecl.Instantiate (n,m,l,c,es) ->
        TopDecl.Instantiate (
            string_charlist n,
            string_charlist m, 
            List.map convert_type l,
            constructor_args_convert c,
            List.map convert_expression es)
    | Prev.TopDecl.Extern (e, n, c, eps, fs) ->
        TopDecl.Extern (
            string_charlist e,
            Nat.of_int n,
            convert_constructor_params c,
            List.map convert_type eps,
            convert_Fields_poly fs string_charlist
            (fun ((ts,exs),arr) ->
             (Nat.of_int ts, List.map string_charlist exs), convert_arrowT arr))
    | Prev.TopDecl.Control (s, c, ts, fs, p, d, st) ->
        TopDecl.Control (
            string_charlist s,
            convert_constructor_params c,
            List.map convert_type ts,
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            List.map controld_convert d,
            stmt_convert st)
    | Prev.TopDecl.Parser (s, c, ts, fs, p, bl, fs2) ->
        TopDecl.Parser (
            string_charlist s, 
            convert_constructor_params c,
            List.map convert_type ts,
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            stmt_convert bl,
            List.map stmt_convert fs2)
    | Prev.TopDecl.Funct (n, l, a, st) ->
        TopDecl.Funct (
            string_charlist n,
            Nat.of_int l, 
            convert_arrowT a,
            stmt_convert st)
