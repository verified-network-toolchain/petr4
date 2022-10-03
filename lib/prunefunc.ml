open Poulet4.Typed
open P4light

let noinfo = P4info.dummy

let noloc = noLocator

let notype = TypVoid

let nodir = InOut

let gen_p4expr (pre_e : coq_ExpressionPreT) : coq_Expression =
  MkExpression (noinfo, pre_e, notype, nodir)
  
let gen_p4stmt (pre_s : coq_StatementPreT) : coq_Statement =
  MkStatement (noinfo, pre_s, StmUnit)

let gen_p4expint (v : int) (w : int) : coq_Expression =
  gen_p4expr
    (ExpInt
       { tags= noinfo
       ; value= Bigint.of_int v
       ; width_signed= Some (Bigint.of_int w, false) } )

let to_p4str s : P4string.t = {tags= noinfo; str= s}

let gen_p4name s : P4name.t = BareName (to_p4str s)

let gen_p4expname (ss : string list) : coq_Expression =
  let rec gen_name' ss : coq_Expression =
    match ss with
    | [] ->
        raise (Invalid_argument "[gen_p4expname] empty argument list.")
    | [s] ->
        gen_p4expr (ExpName (gen_p4name s, noloc))
    | s :: tl ->
        gen_p4expr (ExpExpressionMember (gen_name' tl, to_p4str s))
  in
  gen_name' (List.rev ss)


let gen_p4decltypedef (s : string) (n : int) : coq_Declaration =
  DeclTypeDef (noinfo, to_p4str s, Coq_inl (TypBit (Bigint.of_int n)))

let gen_p4meta (ss : string list) : coq_Expression =
  gen_p4expname ("ig_md" :: ss)

let gen_p4intr_meta (ss : string list) : coq_Expression =
  gen_p4expname ("ig_intr_md" :: ss)

let gen_p4match (pre_m : coq_MatchPreT) : coq_Match =
  MkMatch (noinfo, pre_m, notype)

let gen_p4param (dir : direction) (typ : coq_P4Type) (s : string) :
    coq_P4Parameter =
  MkParameter (false, dir, typ, None, to_p4str s)

let gen_p4actref_na (s : string) : coq_TableActionRef =
  MkTableActionRef (noinfo, MkTablePreActionRef (gen_p4name s, []), notype)

let p4actref_noaction : coq_TableActionRef =
  MkTableActionRef
    ( noinfo
    , MkTablePreActionRef (QualifiedName ([], to_p4str "NoAction"), [])
    , notype )

let gen_p4entry_na (ms : coq_MatchPreT list) (s : string) : coq_TableEntry =
  MkTableEntry (noinfo, List.map gen_p4match ms, gen_p4actref_na s)

let rec stmt_list_to_block (stmts : coq_Statement list) : coq_Block =
  match stmts with
  | [] ->
      BlockEmpty noinfo
  | hd :: tl ->
      BlockCons (hd, stmt_list_to_block tl)

let prestmt_list_to_block (stmts : coq_StatementPreT list) : coq_Block =
  List.map gen_p4stmt stmts |> stmt_list_to_block

let gen_p4act (s : string) (act_body : coq_StatementPreT list) :
    coq_Declaration =
  DeclAction (noinfo, to_p4str s, [], [], prestmt_list_to_block act_body)

let gen_p4tbl (s : string) (a : string) : coq_Declaration =
  DeclTable
    ( noinfo
    , to_p4str s
    , []
    , [gen_p4actref_na a]
    , None
    , Some (gen_p4actref_na a)
    , Some Bigint.one
    , [] )
let gen_p4tbl_call ?(args : string list list = []) (t : string) :
    coq_StatementPreT =
  let args = List.map (fun a -> Some (gen_p4expname a)) args in
  StatMethodCall (gen_p4expname [t; "apply"], [], args)

let gen_p4ctrl ?(cps : (direction * coq_P4Type * string) list = [])  (s : string) (ps : (direction * coq_P4Type * string) list)
    (ds : coq_Declaration list) (ss : coq_StatementPreT list) :
    coq_Declaration =
  DeclControl
    ( noinfo
    , to_p4str s
    , []
    , List.map (fun (d, t, v) -> gen_p4param d t v) ps
    , List.map (fun (d, t, v) -> gen_p4param d t v) cps
    , ds
    , prestmt_list_to_block ss )
