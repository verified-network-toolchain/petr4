open Core_kernel
open StdLabels
open List 
open Util
open Pp 
open Pp.O

module P4 = Types 

let format_list_pp_sep f sep l = 
  Pp.concat_map ~sep l ~f

let format_list_sep f sep l = 
  format_list_pp_sep f (text sep) l

let format_list_nl f l = 
  format_list_sep f "\n" l

let format_option f o =
  match o with
  | None -> nop 
  | Some x -> f x 

let format_list_sep_nl f sep l =
  Pp.concat_map ~sep:((sep |> text) ++ ("\n" |> text)) l ~f:f

module P4Int = struct
  open P4.P4Int
  let format_bigint b = b |> Bigint.to_string |> text
  let format_t e =
    let i = snd e in
    (match i.width_signed with
     | None -> i.value |> format_bigint |> box 
     | Some (width,signed) -> (width |> string_of_int |> text) ++
                              (text (if signed then "s" else "w")) ++
                              (i.value |> format_bigint) |> box) 
end

module P4String = struct 
  let format_t e = ("\"" |> text) ++ (e |> snd |> text) ++ ("\"" |> text)
end

module P4Word = struct 
  let format_t e =  e |> snd |> text
end

let name_format_t (name: Types.name) =
  match name with
  | BareName str -> P4Word.format_t str
  | QualifiedName ([], str) -> (text ".") ++ (P4Word.format_t str)
  | _ -> failwith "illegal name"

module rec Expression : sig
  val format_t : P4.Expression.t -> _ Pp.t 
end = struct
  open P4.Expression
  let rec format_t e =
    match snd e with
    | True ->  text "true" 
    | False -> text "false"
    | Int i -> P4Int.format_t i
    | String s -> P4String.format_t s
    | Name name -> name_format_t name 
    | ArrayAccess x ->
      (format_t x.array) ++ (text "[") ++ (format_t x.index) ++ (text "]") 
      |> box ~indent:2
    | BitStringAccess x -> 
      (format_t x.bits) ++ (text "[") ++ (format_t x.hi) ++ (text ":") ++ 
      (format_t x.lo) ++ (text "]") |> box ~indent:2
    | List x -> (text "{") ++ (format_list_sep format_t ", " x.values) ++ 
                (text "}") |> box ~indent:2 
    | Record x -> (text "{") ++ (format_list_sep KeyValue.format_t ", " x.entries) ++
                  (text "}") |> box ~indent:2
    | UnaryOp x -> 
      let uop = match (snd x.op) with
        | Not -> "!"
        | BitNot -> "~"
        | UMinus -> "-"
      in (uop |> text) ++ (format_t x.arg)
         |> box 
    | BinaryOp x ->
      let bop = match (snd x.op) with
          Plus -> "+"
        | PlusSat -> "|+|"
        | Minus -> "-"
        | MinusSat -> "|-|"
        | Mul -> "*"
        | Div -> "/"
        | Mod -> "%"
        | Shl -> "<<"
        | Shr -> ">>"
        | Le -> "<="
        | Ge -> ">="
        | Lt -> "<"
        | Gt -> ">"
        | Eq -> "=="
        | NotEq -> "!="
        | BitAnd -> " & "
        | BitXor -> " ^ "
        | BitOr -> " | "
        | PlusPlus -> " ++ "
        | And -> " && "
        | Or -> " || "
      in (x.args |> fst |> format_t) ++ (bop |> text) ++
         (format_t (snd x.args)) |> hbox
    | Cast x -> 
      ("(" |> text) ++ (Type.format_t x.typ) ++ (") " |> text) ++
      (format_t x.expr) |> hbox 
    | TypeMember x -> 
      (name_format_t x.typ) ++ ("." |> text) ++ (x.name |> snd |> text) 
      |> box ~indent:2
    | ErrorMember x -> x |> snd |> text 
    | ExpressionMember x -> (format_t x.expr) ++ ("." |> text) ++
                            (x.name |> snd |> text) |> box ~indent:2
    | Ternary x ->
      ("(" |> text) ++ (format_t x.cond) ++ space ++ ("?" |> text) ++
      space ++ (format_t x.tru) ++ space ++ (":" |> text) ++
      space ++ (format_t x.fls) ++ (")" |> text) |> box ~indent:2
    | FunctionCall x ->
      (format_t x.func) ++ (Type.format_typ_args x.type_args) ++ ("(" |> text) ++
      (format_list_sep Argument.format_t ", " x.args) ++ (")" |> text) 
      |> box ~indent:2
    | NamelessInstantiation x ->
      (Type.format_t x.typ) ++ ("(" |> text) ++ 
      (format_list_sep Argument.format_t ", " x.args) ++ (")" |> text) 
      |> box ~indent:2
    | Mask x ->
      (format_t x.expr) ++ space ++ ("&&&" |> text) ++ space ++ (format_t x.mask) 
      |> box ~indent:2
    | Range x -> 
      (format_t x.lo) ++ space ++ (".." |> text) ++ space ++ (format_t x.hi)
      |> box ~indent:2
end 

and Statement : sig 
  val format_t : P4.Statement.t -> _ Pp.t
end = struct 
  open P4.Statement 

  let format_switch_label sl =
    match sl with
    | Default -> text "default"
    | Name(sl) -> sl |> P4Word.format_t |> box ~indent:2

  let format_switch_case sc =
    match snd sc with
    | Action { label; code } ->
      (format_switch_label (snd label)) ++ (": " |> text) ++ 
      (Block.format_t code) ++ ("\n}" |> text)
    | FallThrough { label } ->
      (format_switch_label (snd label)) ++ (":" |> text)

  let block_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      ("else " |> text) ++ (Block.format_t fls_block) ++ ("\n}" |> text)
    | Some sfls -> 
      ("\nelse" |> text) ++ space ++ (Statement.format_t sfls)
      |> box ~indent:2

  let wc_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      ("\n" |> text) ++ (("else " |> text) ++ (Block.format_t fls_block) ++ 
                         ("\n}" |> text)) |> box ~indent:2
    | Some sfls -> 
      ("\n" |> text) ++ (("else" |> text) ++ ("\n" |> text) ++ 
                         (Statement.format_t sfls) |> box ~indent:2) 

  let rec format_t (e:t) =
    match snd e with
    | MethodCall { func; type_args; args } ->
      (Expression.format_t func) ++ (Type.format_typ_args type_args) ++
      ("(" |> text) ++ (box ((Argument.format_ts args) ++
                             (")" |> text) ++ (";" |> text))) |> hvbox
    | Assignment { lhs; rhs } -> 
      (Expression.format_t lhs) ++ space ++ ("=" |> text) ++ space ++ 
      (Expression.format_t rhs) ++ (";" |> text) |> box
    | DirectApplication { typ; args } ->
      (Type.format_t typ) ++ (".apply(" |> text) ++ (Argument.format_ts args) ++
      (");" |> text) |> hvbox 
    | Conditional { cond; tru; fls } ->
      let close = match snd tru with 
        | BlockStatement { block=tru_block } -> 
          ("\n}" |> text) ++ (block_fls fls)
        | _ ->  nop
      in let remainder = match snd tru with 
          | BlockStatement { block=tru_block } -> 
            (tru_block |> Block.format_t) 
          | _ ->  ("\n" |> text) ++ (format_t tru) ++ (wc_fls fls)
      in (box ~indent: 2 (("if" |> text) ++ space ++  ("(" |> text) ++ 
                          (Expression.format_t cond) ++ (")" |> text) ++
                          space ++ remainder)) ++ close 
    | BlockStatement { block } ->
      (block |> Block.format_t |> box ~indent:2) ++ ("\n}" |> text)
    | Exit -> text "exit;"
    | EmptyStatement -> text ";"
    | Return { expr = None } -> text "return;"
    | Return { expr = Some sexpr } ->
      ("return" |> text) ++ (space ++ (Expression.format_t sexpr) ++ 
                             (";" |> text)) |> hvbox 
    | Switch { expr; cases } -> 
      (hvbox ("switch" |> text) ++ space ++ ("(" |> text) ++ 
       (box (Expression.format_t expr)) ++ (")" |> text) ++ space ++ 
       ("{\n" |> text) ++ (format_list_nl format_switch_case cases)) ++ 
      ("\n}" |> text)
    | DeclarationStatement { decl } ->
      Declaration.format_t decl
end   

and Block : sig
  val format_t : P4.Block.t -> _ Pp.t
end = struct
  open P4.Block
  let format_t e =
    match snd e with
    | { annotations=[]; statements=[] } -> "{ " |> text 
    | { annotations; statements } ->
      (Annotation.format_ts annotations) ++ ("{\n" |> text) ++
      (format_list_nl Statement.format_t statements)
end

and Argument : sig
  val format_t : P4.Argument.t -> _ Pp.t
  val format_ts : P4.Argument.t list -> _ Pp.t
end = struct
  open P4.Argument
  let format_t e =
    match snd e with
    | Expression x ->
      x.value |> Expression.format_t |> box ~indent:2
    | KeyValue x ->
      (x.key |> snd |> text) ++ (("=" |> text) ++ (Expression.format_t x.value)) 
      |> box ~indent:2
    | Missing -> text "_"
  let format_ts l =
    format_list_sep format_t ", " l |> box ~indent:2
end

and Type : sig
  val format_t : P4.Type.t -> _ Pp.t
  val format_typ_args: P4.Type.t list -> _ Pp.t
  val format_type_params: P4.P4String.t list -> _ Pp.t
end = struct
  open P4.Type
  let rec format_t e =
    match snd e with
    | Bool -> text "bool"
    | Error -> text "error"
    | Integer -> text "int"
    | IntType x -> ("int" |> text) ++ ("<" |> text) ++ 
                   ( Expression.format_t x) ++ (">" |> text) |> box 
    | BitType e -> 
      begin match snd e with 
        | P4.Expression.Int _  -> 
          ("bit<" |> text) ++ (Expression.format_t e) ++ (">" |> text)
          |> box ~indent:2
        | _ -> 
          ("bit<(" |> text) ++ (Expression.format_t e) ++ (")>" |> text) 
          |> box ~indent:2
      end
    | VarBit x ->
      ("varbit" |> text) ++ space ++ ("<" |> text) ++ ( Expression.format_t x) ++
      (">" |> text) |> box ~indent:2
    | TypeName (BareName x) -> x |> snd |> text |> box ~indent:2
    | TypeName (QualifiedName ([], x)) ->
      ("." |> text) ++ (x |> snd |> text) |> box ~indent:2
    | TypeName _ -> failwith "unimplemented" 
    | SpecializedType x -> 
      (format_t x.base) ++ ("<" |> text) ++ 
      (format_list_sep format_t ", " x.args) ++ 
      (">" |> text) |> box~indent:2
    | HeaderStack x -> 
      (format_t x.header) ++ ("[" |> text) ++ 
      (Expression.format_t x.size) ++ ("]" |> text) |> box ~indent:2  
    | Tuple x -> ("tuple<" |> text) ++ (format_list_sep format_t ", " x) ++ 
                 (">" |> text) |> box ~indent:2
    | String -> text "string"      
    | Void -> text "void"
    | DontCare -> text "_"

  let format_typ_args l =
    if List.length l = 0 then nop 
    else
      ("<" |> text) ++ (format_list_sep format_t ", " l) ++ (">" |> text)

  let format_type_params l =
    if  List.length l = 0 then nop 
    else
      ("<" |> text) ++ (format_list_sep P4Word.format_t ", " l) ++ (">" |> text)
end

and KeyValue : sig 
  val format_t : P4.KeyValue.t -> _ Pp.t
end = struct
  open P4.KeyValue
  let format_t kv = 
    match snd kv with 
    | { key; value } -> 
      (P4Word.format_t key) ++ space ++ ("=" |> text) ++ space ++ (Expression.format_t value) |> box ~indent:2
end

and Annotation : sig
  val format_t : P4.Annotation.t -> _ Pp.t
  val format_ts : P4.Annotation.t list -> _ Pp.t
end = struct
  open P4.Annotation
  let format_body body = 
    match snd body with 
    | Empty -> nop 
    | Unparsed strings -> 
      ("(" |> text) ++ (format_list_sep P4Word.format_t " " strings) ++
      (")" |> text)
    | Expression exprs -> 
      ("[" |> text) ++ (format_list_sep Expression.format_t ", " exprs) ++
      ("]" |> text)
    | KeyValue kvs -> 
      ("[" |> text) ++ (format_list_sep KeyValue.format_t ", " kvs) ++ 
      ("]" |> text) |> hovbox ~indent:2

  let format_t e =
    match snd e with 
    | { name; body } -> 
      ("@" |> text) ++ (P4Word.format_t name) ++ (format_body body) |> box 

  let format_ts l =
    match l with
    | [] -> nop 
    | _ :: _ -> (format_list_nl format_t l) ++ ("\n" |> text)
end

and Direction : sig
  val format_t : P4.Direction.t -> _ Pp.t
end = struct
  open P4.Direction
  let format_t e =
    match snd e with
    | In -> text "in"
    | Out -> text "out"
    | InOut -> text "inout"
end

and Parameter : sig
  val format_t : P4.Parameter.t -> _ Pp.t
  val format_params : P4.Parameter.t list -> _ Pp.t
  val format_constructor_params : P4.Parameter.t list -> _ Pp.t
end = struct
  open P4.Parameter
  let format_dir d =
    match d with
    | Some d -> Direction.format_t d ++ space
    | None -> nop

  let format_opt_value v =
    match v with
    | Some v -> text "=" ++ space ++ Expression.format_t v
    | None -> nop

  let format_t (_, p) =
    hovbox @@
    Annotation.format_ts p.annotations
    ++ format_dir p.direction
    ++ Type.format_t p.typ
    ++ space
    ++ P4Word.format_t p.variable
    ++ format_opt_value p.opt_value

  let format_params l = format_list_pp_sep format_t (text "," ++ space) l 

  let format_constructor_params l =
    match l with
    | [] -> nop
    | _ :: _ ->
      text "("
      ++ (box ~indent:2 (format_list_pp_sep format_t (text "," ++ space) l)) 
      ++ text ")"
end

and Match: sig
  val format_t : P4.Match.t -> _ Pp.t 
  val format_ts : P4.Match.t list -> _ Pp.t 
end = struct
  open P4.Match
  let format_t e =
    match snd e with
    | Default -> text "default"
    | DontCare -> text "_"
    | Expression { expr } ->
      Expression.format_t expr

  let format_ts  l =
    match l with
    | [] -> nop 
    | [x] -> format_t x
    | _ -> ("(" |> text) ++ (box (format_list_sep format_t ", " l)) ++ 
           (")" |> text) |> box ~indent:2 
end

and Parser : sig
  val format_state : P4.Parser.state -> _ Pp.t
  val format_states : P4.Parser.state list -> _ Pp.t
end = struct
  open P4.Parser

  let format_case e =
    match snd e with
    | { matches; next } ->
      (Match.format_ts matches) ++ (":" |> text) ++ space ++ 
      (P4Word.format_t next) ++ (";" |> text)

  let format_transition e =
    match snd e with
    | Direct { next } -> 
      ("transition" |> text) ++ space ++ (P4Word.format_t next) ++ (";" |> text)
    | Select { exprs; cases } ->
      (box ~indent:2 
         (("transition" |> text) ++ space ++ ("select(" |> text) ++ 
          (format_list_sep Expression.format_t ", " exprs) ++
          (")" |> text) ++ 
          (begin match cases with
             | [] -> " {" |> text
             | _ -> (" {\n" |> text) ++ 
                    (format_list_nl format_case cases) end))) ++ 
      ("\n}" |> text)

  let format_state e =
    match snd e with
    | { annotations; name; statements; transition } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("state" |> text) ++ 
                      space ++ 
                      (P4Word.format_t name) ++ 
                      space ++
                      ("{\n" |> text) ++ 
                      (format_list_nl Statement.format_t statements) ++ 
                      (match statements with 
                       | [] -> nop 
                       | _ :: _ -> text "\n") ++
                      (format_transition transition))) ++ 
      ("\n}" |> text)

  let format_states l =
    format_list_nl format_state l
end

and Table : sig 
  val format_property : P4.Table.property -> _ Pp.t
end = struct 
  open P4.Table 

  let format_key e = 
    match snd e with 
    | { annotations; key; match_kind } -> 
      box ~indent:2 ((Expression.format_t key) ++ (":" |> text) ++ space ++ 
                     (P4Word.format_t match_kind) ++ 
                     (Annotation.format_ts annotations) ++ (";" |> text))

  let format_action_ref e = 
    match snd e with 
    | { annotations; name; args = [] } ->
      (Annotation.format_ts annotations) ++ 
      (name |> name_format_t |> box ~indent:2)
    | { annotations; name; args } ->
      (Annotation.format_ts annotations) ++
      (box ~indent:2 ((name_format_t name) ++ 
                      ("(" |> text) ++ (box (Argument.format_ts args)) ++  
                      (")" |> text)))

  let format_entry e =
    match snd e with
    | { annotations; matches; action } ->
      (box ~indent:2 ((Match.format_ts matches) ++ (":" |> text) ++ 
                      space ++ (format_action_ref action))) ++ 
      ((Annotation.format_ts annotations) ++ (";" |> text))

  let format_property e = 
    match snd e with 
    | Key  { keys } ->
      (box ~indent:2 (("key" |> text) ++ space ++ ("=" |> text) ++ space ++
                      ("{\n" |> text) ++ (format_list_nl format_key keys))) ++
      ("\n}" |> text)
    | Actions { actions } ->
      (box ~indent:2 (("actions" |> text) ++ space ++ ("=" |> text) ++ space ++
                      ("{\n" |> text) ++ 
                      (format_list_sep format_action_ref ";" actions) ++ 
                      (begin match actions with
                         | [] -> nop
                         | _ -> ";" |> text end))) ++
      ("\n}" |> text)
    | Entries { entries } ->
      (box ~indent:2 (("const entries" |> text) ++ space ++ ("=" |> text) ++
                      space ++ ("{\n" |> text) ++ 
                      (format_list_nl format_entry entries))) ++
      ("\n}" |> text)
    | Custom { annotations; const; name; value } ->
      (Annotation.format_ts annotations) ++
      (box ~indent:2 (((if const then "const " else "") |> text) ++ 
                      (P4Word.format_t name) ++ space ++ ("=" |> text) ++
                      space ++ (Expression.format_t value) ++ 
                      (";" |> text)))
end 

and MethodPrototype : sig
  val format_t : P4.MethodPrototype.t -> _ Pp.t
end = struct
  open P4.MethodPrototype
  let format_t e =
    match snd e with
    | Constructor { annotations; name; params } ->
      (Annotation.format_ts annotations) ++
      (box ~indent:2 ((P4Word.format_t name) ++
                      (" (" |> text) ++
                      (vbox (Parameter.format_params params)) ++
                      (");" |> text)))
    | Method { annotations; return; name; type_params; params } ->
      Annotation.format_ts annotations
      ++ hbox (Type.format_t return
               ++ space
               ++ P4Word.format_t name
               ++ Type.format_type_params type_params
               ++ text "(")
      ++ vbox (Parameter.format_params params ++ text ");")
    | AbstractMethod { annotations; return; name; type_params; params } -> 
      (Annotation.format_ts annotations) ++
      (box ~indent:2 (("abstract" |> text) ++ space ++ (Type.format_t return) ++ 
                      space ++ (P4Word.format_t name) ++ 
                      (Type.format_type_params type_params) ++
                      (" (" |> text) ++
                      (vbox (Parameter.format_params params)) ++ 
                      (");" |> text)))
end

and Declaration : sig
  val format_t : P4.Declaration.t -> _ Pp.t
end = struct
  open P4.Declaration

  let format_field f =
    match snd f with
    | { annotations; typ; name } ->
      (annotations |> Annotation.format_ts |> box) ++
      (box ~indent:2 ((Type.format_t typ) ++ space ++ (P4Word.format_t name) ++
                      (";" |> text)))

  let format_typ_or_decl td =
    match td with
    | Left(typ) ->
      Type.format_t typ
    | Right(decl) ->
      Declaration.format_t decl


  let rec dec_help locals = 
    if not (List.length locals = 0) then 
      (format_list_sep format_t "\n" locals) ++ ("\n" |> text)
    else nop 

  and format_t e = 
    match snd e with 
    | Constant { annotations; typ; name; value } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("const" |> text) ++
                      space ++ (Type.format_t typ) ++
                      space ++
                      (name |> snd |> text) ++
                      space ++ 
                      ("=" |> text) ++ 
                      space ++ 
                      (Expression.format_t value) ++
                      (";" |> text)))
    | Action { annotations; name; params; body } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2
         (("action" |> text) ++ space ++ (name |> snd |> text) ++ ("(" |> text) ++ 
          (vbox (Parameter.format_params params)) ++ (") " |> text) ++
          (Block.format_t body))) ++ ("\n}" |> text)
    | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2
         (("control" |> text) ++ (space ++ (name |> snd |> text) ++
                                  (Type.format_type_params type_params) ++ 
                                  ("(" |> text) ++ 
                                  (vbox (Parameter.format_params params)) ++ 
                                  (")" |> text) ++ 
                                  (Parameter.format_constructor_params constructor_params) ++ 
                                  (" {\n" |> text) ++ 
                                  (dec_help locals) ++ 
                                  (box ~indent: 2 (("apply " |> text) ++ 
                                                   (Block.format_t apply))) ++
                                  ("\n}" |> text))) ++ 
       ("\n}" |> text))
    | Parser { annotations; name; type_params; params; constructor_params; locals; states } -> 
      (box ~indent:2 
         ((Annotation.format_ts annotations)  ++ 
          ("parser" |> text) ++ 
          (space ++  
           (name |> snd |> text) ++ 
           (Type.format_type_params type_params) ++ 
           (" (" |> text) ++ 
           (vbox (Parameter.format_params params)) ++ 
           (")" |> text) ++ 
           (Parameter.format_constructor_params constructor_params) ++ 
           (" {\n" |> text)) ++ 
          (dec_help locals) ++ (Parser.format_states states)))  ++ 
      ("\n}\n" |> text)
    | Instantiation { annotations; typ; args; name; init=None } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 ((Type.format_t typ) ++ 
                      ("(" |> text) ++ 
                      (box (Argument.format_ts args)) ++ 
                      (")" |> text) ++ 
                      space  ++ 
                      (P4Word.format_t name) ++ 
                      (";" |> text)))
    | Instantiation { annotations; typ; args; name; init=Some block } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent: 2
         (Type.format_t typ) ++ 
       ("(" |> text) ++ 
       (box (Argument.format_ts args))  ++ 
       (")" |> text) ++ 
       space ++ 
       (P4Word.format_t name) ++ 
       space ++ 
       ("= " |> text) ++ 
       (Block.format_t block)) ++ 
      ("\n};" |> text)
    | Table { annotations; name; properties } -> 
      (box ~indent:2 ((Annotation.format_ts annotations) ++ 
                      ("table" |> text) ++ 
                      space  ++ 
                      (P4Word.format_t name) ++ 
                      (" {\n" |> text) ++ 
                      (format_list_nl Table.format_property properties))) ++  
      ("\n}" |> text)  
    | Variable { annotations; typ; name; init = None } ->
      (Annotation.format_ts annotations) ++  
      (box ~indent:2 ( (Type.format_t typ) ++ 
                       space ++ (P4Word.format_t name) ++
                       (";" |> text)))
    | Variable { annotations; typ; name; init = Some sinit } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 ((Type.format_t typ) ++
                      space  ++
                      (P4Word.format_t name) ++
                      space  ++
                      ("=" |> text) ++
                      space ++ (Expression.format_t sinit) ++
                      (";" |> text)))                             
    | ExternFunction { annotations; return; name; type_params; params } ->
      Annotation.format_ts annotations
      ++ text "extern"
      ++ text " "
      ++ Type.format_t return
      ++ text " "
      ++ hbox (P4Word.format_t name
               ++ Type.format_type_params type_params
               ++ text "(")
      ++ box (Parameter.format_params params ++ text ");")
    (* Annotation.format_ts annotations
       ++ (box ~indent:2 (text "extern") 
        ++ text " "
        ++ Type.format_t return
        ++ text " "
        ++ (P4Word.format_t name
            ++ Type.format_type_params type_params
            ++ text "(")
        ++ vbox (Parameter.format_params params ++ text ");")) *)
    | Function { return; name; type_params; params; body } ->
      (box ~indent:2 ((Type.format_t return) ++ 
                      space  ++ 
                      (P4Word.format_t name) ++ 
                      (Type.format_type_params type_params) ++ 
                      (" (" |> text) ++ 
                      (vbox (Parameter.format_params params)) ++ 
                      (") " |> text) ++ 
                      (Block.format_t body))) ++ 
      ("\n}" |> text)
    | ValueSet { annotations; typ; size; name } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("value_set<" |> text) ++ (Type.format_t typ) ++
                      (">(" |> text) ++ (box (Expression.format_t size)) ++
                      (")" |> text) ++ space ++ (P4Word.format_t name) ++
                      (";" |> text)))
    | TypeDef { annotations; name; typ_or_decl } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("typedef" |> text) ++ 
                      space ++ (format_typ_or_decl typ_or_decl) ++ space ++ 
                      (name |> snd |> text) ++ (";" |> text)))
    | ControlType { annotations; name; type_params; params } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("control" |> text) ++ space ++ (name |> snd |> text) ++ 
                      (Type.format_type_params type_params) ++
                      (" (" |> text) ++ 
                      (vbox (format_list_sep Parameter.format_t ", " params)) ++
                      (");" |> text)))
    | ParserType { annotations; name; type_params; params } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 
         (("parser" |> text) ++ space ++ (name |> snd |> text) ++ 
          (Type.format_type_params type_params) ++ (" (" |> text) ++
          (vbox (format_list_sep Parameter.format_t ", " params)) ++ 
          (");" |> text)))
    | PackageType { annotations; name; type_params; params } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 
         (("package" |> text) ++
          space ++ 
          (name |> snd |> text) ++ 
          (Type.format_type_params type_params) ++ 
          (" (" |> text) ++ 
          (vbox (format_list_sep Parameter.format_t ", " params)) ++ 
          (");" |> text)))
    | Struct { annotations; name; fields } -> 
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("struct" |> text) ++ 
                      space ++ 
                      (P4Word.format_t name) ++ 
                      (begin match fields with
                         | [] -> " {" |> text
                         | _ -> (" {\n" |> text) ++ 
                                (format_list_nl format_field fields) end))) ++ 
      ("\n}" |> text)
    | MatchKind { members=[] } ->
      "match_kind {\n}" |> text |> box
    | MatchKind { members } ->
      (box ~indent:2 (("match_kind" |> text) ++ space ++ ("{\n" |> text) ++ 
                      (format_list_sep P4Word.format_t ", " members))) ++ 
      ("\n}" |> text)
    | Error { members=[] } ->
      box ("error {\n}" |> text)
    | Error { members } ->
      (box ~indent:2 (("error {" |> verbatim) ++ 
                      newline ++
                      (format_list_sep P4Word.format_t ", " members))) ++ 
      ("\n}" |> text)
    | Enum { annotations; name; members=[] } ->
      (Annotation.format_ts annotations) ++
      (box ~indent:2 (("enum" |> text) ++ space ++  (P4Word.format_t name) ++
                      space ++ ("{\n}" |> text)))
    | Enum { annotations; name; members } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2
         (("enum" |> text) ++ space ++ (P4Word.format_t name) ++ space ++ 
          ("{\n" |> text) ++ (format_list_sep P4Word.format_t ", \n" members))) ++
      ("\n}" |> text)
    | SerializableEnum { annotations; typ; name; members=[] } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("enum" |> text) ++ 
                      space  ++ (Type.format_t typ) ++ space ++ (P4Word.format_t name) ++
                      space  ++ ("{" |> text) ++ newline  ++ ("}" |> text)))
    | SerializableEnum { annotations; typ; name; members } ->
      let format_member (field,init) =
        (P4Word.format_t field) ++ space ++ ("=" |> text) ++ space ++ 
        (Expression.format_t init) in 
      (Annotation.format_ts annotations) ++ 
      (box ~indent: 2
         (("enum" |> text) ++ space ++ (Type.format_t typ) ++
          space ++ (P4Word.format_t name) ++ (" {\n" |> text) ++
          (format_list_sep format_member ", \n" members))) ++ 
      ("\n}" |> text)   
    | ExternObject { annotations; name; type_params; methods = [] } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2
         (("extern" |> text) ++
          space  ++
          (P4Word.format_t name) ++
          space  ++
          (Type.format_type_params type_params) ++
          space  ++
          ("{" |> text) ++
          newline  ++
          ("}" |> text)))
    | ExternObject { annotations; name; type_params; methods } ->   
      seq (seq (Annotation.format_ts annotations)
             (box ~indent:2 
                (seq (hvbox ~indent:2 ((seq ("extern" |> text)
                                          (seq space 
                                             (seq (P4Word.format_t name)
                                                (seq (Type.format_type_params type_params)
                                                   (" {\n" |> text)))))))
                   (format_list_nl MethodPrototype.format_t methods))))
        ("\n}\n" |> text) 
    | Header { annotations; name; fields } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 
         (("header" |> text) ++ 
          space ++
          (P4Word.format_t name) ++
          (begin match fields with
             | [] -> " {" |> text
             | _ -> (" {\n" |> text) ++ 
                    (format_list_nl format_field fields) end))) ++
      ("\n}" |> text)
    | HeaderUnion { annotations; name; fields } ->
      (Annotation.format_ts annotations) ++ 
      (box ~indent:2 (("header_union" |> text) ++ 
                      space ++ 
                      (P4Word.format_t name) ++ 
                      (begin match fields with
                         | [] -> " {" |> text
                         | _ -> (" {\n" |> text) ++ 
                                (format_list_nl format_field fields) end))) ++
      ("\n}" |> text)
    | NewType { annotations; name; typ_or_decl } ->
      box ~indent:2 ((Annotation.format_ts annotations) ++ 
                     ("type" |> text) ++ 
                     space  ++ 
                     (format_typ_or_decl typ_or_decl) ++ 
                     space  ++ 
                     (name |> snd |> text) ++ 
                     (";" |> text))
end 

let format_program p =
  match p with
  | P4.Program(ds) ->
    box ((format_list_nl Declaration.format_t ds) ++ 
         ("\n" |> text))

