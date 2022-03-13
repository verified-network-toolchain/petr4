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
    | Prev.PADirLess a -> PADirLess a

let convert_paramarg_poly (x : ('a,'b) Prev.paramarg) (funa: 'a -> 'c)
    (funb : 'b -> 'd) = 
    match x with 
    | Prev.PAIn a -> PAIn (funa a)
    | Prev.PAOut b -> PAOut (funb b) 
    | Prev.PAInOut b -> PAInOut (funb b)
    | Prev.PADirLess a -> PADirLess (funa a)

let sum_convert_poly (x: ('a,'b) Poulet4.Datatypes.sum)
    (funa : 'a -> 'c) (funb : 'b -> 'd) =
    match x with 
    | Poulet4.Datatypes.Coq_inl a -> 
        Poulet4_Ccomp.Datatypes.Coq_inl (funa a)
    | Poulet4.Datatypes.Coq_inr b -> 
        Poulet4_Ccomp.Datatypes.Coq_inr (funb b)

let convert_Field (x: ('k, 'v) Prev.F.f) : ('k,'v) F.f =
    (fst x, snd x)

let convert_Field_poly (x: ('k, 'v) Prev.F.f) (funk : 'k -> 'k1)
(funv : 'v -> 'v1): ('k1,'v1) F.f =
    (funk (fst x), funv (snd x))

let convert_Fields (x: ('k, 'v) Prev.F.fs) : ('k,'v) F.fs =
    List.map (convert_Field) x

let convert_Fields_poly (x: ('k, 'v) Prev.F.fs) (funk : 'k -> 'k1)
(funv : 'v -> 'v1): ('k1,'v1) F.fs  =
    List.map (fun x -> convert_Field_poly x funk funv) x


let convert_arrow (x : ('k,'a,'b,'r) Prev.arrow) 
: ('k,'a,'b,'r) arrow =
    {
        paramargs = 
            List.map (fun y -> (fst y, convert_paramarg(snd y))) (convert_Fields x.paramargs);
        rtrns = x.rtrns;
    }

let convert_arrow_poly (x : ('k,'a,'b,'r) Prev.arrow)
    (funk : 'k -> 'k1)
    (funa : 'a -> 'a1)
    (funb : 'b -> 'b1)
    (funr : 'r -> 'r1)
    : ('k1,'a1,'b1,'r1) arrow = 
    {
        paramargs = 
            List.map 
            (fun y -> (funk (fst y), convert_paramarg_poly (snd y) funa funb)) 
            (convert_Fields x.paramargs);
        rtrns = Option.map funr x.rtrns;
    }


let rec convert_type (x : Prev.Expr.t) =
    match x with 
    | Prev.Expr.TBool -> Expr.TBool
    | Prev.Expr.TBit i -> Expr.TBit (bigint_coqN i)
    | Prev.Expr.TInt i -> Expr.TInt (bigint_positive i)
    | Prev.Expr.TError -> Expr.TError
    | Prev.Expr.TTuple l -> Expr.TTuple (List.map convert_type l) 
    | Prev.Expr.TStruct fs -> Expr.TStruct (List.map (fun y -> 
    (string_charlist (fst y), (convert_type (snd y)))) (convert_Fields fs))
    | Prev.Expr.THeader fs -> Expr.THeader(List.map (fun y -> 
    (string_charlist (fst y), (convert_type (snd y)))) (convert_Fields fs))
    | Prev.Expr.THeaderStack (fs, i) -> Expr.THeaderStack
    ( (List.map (fun y -> 
    (string_charlist (fst y), (convert_type (snd y)))) (convert_Fields fs)),
        bigint_positive i    
    )
    | Prev.Expr.TVar s -> Expr.TVar (string_charlist s)


let convert_params (fs) = 
    convert_Fields_poly fs 
    string_charlist
    (fun x -> convert_paramarg_poly x convert_type convert_type)

let convert_arrowT (a) = 
    convert_arrow_poly a string_charlist convert_type convert_type convert_type


let rec convert_ct (c) =
    match c with 
    | Prev.Expr.CTType t -> Expr.CTType (convert_type t)
    | Prev.Expr.CTControl (a,b,c) -> Expr.CTControl (
        convert_Fields_poly a string_charlist convert_ct,
        convert_Fields_poly b string_charlist string_charlist,
        convert_params c
    )
    | Prev.Expr.CTParser (a,b,c) -> Expr.CTParser (
        convert_Fields_poly a string_charlist convert_ct,
        convert_Fields_poly b string_charlist string_charlist,
        convert_params c
    )
    | Prev.Expr.CTPackage (fs) -> Expr.CTPackage (
        convert_Fields_poly fs string_charlist convert_ct
    )
    | Prev.Expr.CTExtern (s) -> Expr.CTExtern (
        string_charlist s
    )

let convert_constructor_params (c) = 
    convert_Fields_poly c string_charlist convert_ct


let convert_uop (u:Prev.Expr.uop) =
    match u with
    | Prev.Expr.Not -> Expr.Not
    | Prev.Expr.BitNot -> Expr.BitNot 
    | Prev.Expr.UMinus -> Expr.UMinus
    | Prev.Expr.IsValid -> Expr.IsValid
    | Prev.Expr.SetValid -> Expr.SetValid
    | Prev.Expr.SetInValid -> Expr.SetInValid
    | Prev.Expr.NextIndex -> Expr.NextIndex 
    | Prev.Expr.Size -> Expr.Size

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

let convert_matchkind (m: Prev.Expr.matchkind) =
    match m with
    | Prev.Expr.MKExact -> Expr.MKExact
    | Prev.Expr.MKTernary -> Expr.MKTernary
    | Prev.Expr.MKLpm -> Expr.MKLpm

let rec convert_expression (x : 'tags_t Prev.Expr.e) = match x with
    | Prev.Expr.EBool (b, i) -> Expr.EBool (b, i)
    | Prev.Expr.EBit (w,v,i) -> 
        Expr.EBit ( bigint_coqN w,
        bigint_coqZ v,
        i
        )
    | Prev.Expr.EInt (w,v,i) -> 
        Expr.EInt ( bigint_positive w,
        bigint_coqZ v,
        i
        )
    | Prev.Expr.EVar (t,n,i) ->
        Expr.EVar (convert_type t,
            string_charlist n, i
         )
    | Prev.Expr.ESlice (e, a, b, i) ->
        Expr.ESlice (convert_expression e,
        bigint_positive a, bigint_positive b, i)
    | Prev.Expr.ECast (t, e, i)->
        Expr.ECast (convert_type t, 
        convert_expression e, i)
    | Prev.Expr.EUop (t,u,e,i) ->
        Expr.EUop (convert_type t,
        convert_uop u,
        convert_expression e, i)
    | Prev.Expr.EBop (t,b,e,f,i) ->
        Expr.EBop (convert_type t,
        convert_bop b, 
        convert_expression e,
        convert_expression f, i)
    | Prev.Expr.ETuple (l,i) ->
        Expr.ETuple (
            List.map convert_expression l, i
        )
    | Prev.Expr.EStruct (fs,i) -> 
        Expr.EStruct (
            convert_Fields_poly fs string_charlist convert_expression, i
        )
    | Prev.Expr.EHeader (fs,e,i) ->
        Expr.EHeader (
            convert_Fields_poly fs string_charlist convert_expression,
            convert_expression e, i
        )
    | Prev.Expr.EExprMember(t,s,e,i) ->
        Expr.EExprMember(convert_type t, 
        string_charlist s,
        convert_expression e,i)
    | Prev.Expr.EError (s,i) ->
        Expr.EError(Option.map string_charlist s,
        i)
    | Prev.Expr.EHeaderStack (fs, el, z, i) ->
        Expr.EHeaderStack(convert_Fields_poly fs string_charlist convert_type,
        List.map convert_expression el, 
        bigint_coqZ z, i)
    | Prev.Expr.EHeaderStackAccess (fs, e, z, i) -> 
        Expr.EHeaderStackAccess(convert_Fields_poly fs string_charlist convert_type,
        convert_expression e, 
        bigint_coqZ z, i)


let args_convert (a: 'tags_t Prev.Expr.args) : ('tags_t Expr.args)=
    convert_Fields_poly a string_charlist
    (fun x -> convert_paramarg_poly x convert_expression convert_expression)

let arrowE_convert (a : 'tags_t Prev.Expr.arrowE) =
    convert_arrow_poly a 
    string_charlist
    convert_expression
    convert_expression
    convert_expression

let constructor_arg_convert (c: 'tags_t Prev.Expr.constructor_arg) =
    match c with 
    | Prev.Expr.CAExpr e -> Expr.CAExpr (convert_expression e)
    | Prev.Expr.CAName s -> Expr.CAName (string_charlist s)

let constructor_args_convert (c : 'tags_t Prev.Expr.constructor_args) =
    convert_Fields_poly c 
    string_charlist constructor_arg_convert

let hsop_convert (h: Prev.Stmt.hsop) = 
    match h with 
    | Prev.Stmt.HSPush -> Stmt.HSPush
    | Prev.Stmt.HSPop -> Stmt.HSPop 

let rec stmt_convert (s: 'tags_t Prev.Stmt.s) = 
    match s with
    | Prev.Stmt.SSkip i -> Stmt.SSkip i
    | Prev.Stmt.SVardecl (s, e, i) -> 
        Stmt.SVardecl (string_charlist s,
        sum_convert_poly e convert_type convert_expression,
        i 
        )
    | Prev.Stmt.SAssign (x,y,i) ->
        Stmt.SAssign (convert_expression x,
        convert_expression y, i)
    | Prev.Stmt.SConditional (e,x,y,i) ->
        Stmt.SConditional (convert_expression e,
        stmt_convert x, stmt_convert y,i)
    | Prev.Stmt.SSeq (x,y,i) -> 
        Stmt.SSeq (stmt_convert x,
        stmt_convert y, i)
    | Prev.Stmt.SBlock (x) ->
        Stmt.SBlock (
            stmt_convert s
        )
    | Prev.Stmt.SExternMethodCall (n,m,l,a,i) ->
        Stmt.SExternMethodCall (string_charlist n,
        string_charlist m, 
        List.map convert_type l, 
        arrowE_convert a, i)
    | Prev.Stmt.SFunCall (n,l,a,i) ->
        Stmt.SFunCall (string_charlist n,
        List.map convert_type l,
        arrowE_convert a, i)
    | Prev.Stmt.SActCall (n,a,i) ->
        Stmt.SActCall (string_charlist n,
        args_convert a, i)
    | Prev.Stmt.SReturn (e,i) ->
        Stmt.SReturn (Option.map convert_expression e, 
        i)
    | Prev.Stmt.SExit i ->
        Stmt.SExit i
    | Prev.Stmt.SInvoke (s,i) ->
        Stmt.SInvoke (string_charlist s,i)
    | Prev.Stmt.SApply (s, fs, a, i) ->
        Stmt.SApply (string_charlist s,
        convert_Fields_poly fs string_charlist string_charlist,
        args_convert a, i)
    | Prev.Stmt.SHeaderStackOp (s, h, n, i) ->
        Stmt.SHeaderStackOp(string_charlist s,
        hsop_convert h, bigint_positive n, i)
    | Prev.Stmt.SSetValidity (e, b, i) ->
        SSetValidity (convert_expression e, 
        b, i)

let state_convert (s: Prev.Parser.state) : Parser.state = 
    match s with 
    | Prev.Parser.STStart ->Parser.STStart
    | Prev.Parser.STAccept ->Parser.STAccept 
    | Prev.Parser.STReject ->Parser.STReject 
    | Prev.Parser.STName s ->Parser.STName (string_charlist s)

let rec pat_convert (p: Prev.Parser.pat) : Parser.pat = 
    match p with 
    | Prev.Parser.PATWild ->  Parser.PATWild
    | Prev.Parser.PATMask (p,q) -> Parser.PATMask (pat_convert p, pat_convert q)
    | Prev.Parser.PATRange (p,q) -> Parser.PATRange (pat_convert p, pat_convert q)
    | Prev.Parser.PATBit (i,j) -> Parser.PATBit (bigint_coqN i, bigint_coqZ j)
    | Prev.Parser.PATInt (i,j) -> Parser.PATInt (bigint_positive i, bigint_coqZ j)
    | Prev.Parser.PATTuple (l) -> Parser.PATTuple (List.map pat_convert l)

let rec pae_convert (e : 'tags_t Prev.Parser.e) =
    match e with 
    | Prev.Parser.PGoto (s,i) -> 
        Parser.PGoto(state_convert s, i)
    | Prev.Parser.PSelect (ex,e,fs,i) ->
        Parser.PSelect(convert_expression ex, 
        pae_convert e, 
        convert_Fields_poly fs pat_convert pae_convert,
        i)

let state_block_convert (st: 'tags_t Prev.Parser.state_block) : 
    'tags_t Parser.state_block =
    {
        stmt = stmt_convert (st.stmt);
        trans = pae_convert (st.trans);
    }

let table_convert (t : 'tags_t Prev.Control.table): 'tags_t Control.table 
=
{
    table_key = List.map (fun x -> 
    (convert_expression (fst x), convert_matchkind (snd x))
    ) t.table_key;
    table_actions = List.map string_charlist t.table_actions;
}

let rec controld_convert (d : 'tags_t Prev.Control.d) = 
    match d with 
    | Prev.Control.CDAction (s, p, st, i) ->
        Control.CDAction(
            string_charlist s,
            convert_params p,
            stmt_convert st, i
        )
    | Prev.Control.CDTable (s, t, i) ->
        Control.CDTable(
            string_charlist s,
            table_convert t,
            i
        )
    | Prev.Control.CDSeq (x, y, i) ->
        Control.CDSeq(
            controld_convert x,
            controld_convert y, i
        )

let rec topdecl_convert (d: 'tags_t Prev.TopDecl.d) = 
    match d with 
    | Prev.TopDecl.TPInstantiate (n,m,l,c,i) ->
        TopDecl.TPInstantiate (
            string_charlist n,
            string_charlist m, 
            List.map convert_type l,
            constructor_args_convert c,i
        )
    | Prev.TopDecl.TPExtern (n,l,c, fs,i) ->
        TopDecl.TPExtern (
            string_charlist n,
            List.map string_charlist l,
            convert_constructor_params c,
            convert_Fields_poly fs string_charlist 
            (fun x -> (List.map string_charlist (fst x), convert_arrowT (snd x))),
            i
        )
    | Prev.TopDecl.TPControl (s, c, fs, p, d, st, i) ->
        TopDecl.TPControl (
            string_charlist s,
            convert_constructor_params c,
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            controld_convert d,
            stmt_convert st, i
        )
    | Prev.TopDecl.TPParser (s, c,fs, p, bl, fs2, i) ->
        TopDecl.TPParser (
            string_charlist s, 
            convert_constructor_params c, 
            convert_Fields_poly fs string_charlist string_charlist,
            convert_params p,
            state_block_convert bl,
            convert_Fields_poly fs2 string_charlist state_block_convert,
            i
        )
    | Prev.TopDecl.TPFunction (n, l, a, st, i) ->
        TopDecl.TPFunction (
            string_charlist n,
            List.map string_charlist l, 
            convert_arrowT a,
            stmt_convert st, i
        )
    | Prev.TopDecl.TPSeq (x,y,i) ->
        TPSeq (
            topdecl_convert x,
            topdecl_convert y, i
        )
