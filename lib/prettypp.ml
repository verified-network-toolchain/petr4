open Core_kernel
open StdLabels
open List 
open Util
open Pp 

module P4 = Types 

let format_list_sep f sep l = 
  Pp.concat_map ~sep:(sep |> text) l ~f:f

let format_list_nl f l = 
  Pp.concat_map ~sep:("\n" |> text) l ~f:f

let format_option f o =
  match o with
  | None -> nop 
  | Some x -> f x 

let format_list_sep_nl f sep l =
  Pp.concat_map ~sep:(seq (sep |> text) ("\n" |> text)) l ~f:f

module P4Int = struct
  open P4.P4Int
  let format_bigint b = b |> Bigint.to_string |> text
  let format_t e =
    let i = snd e in
    (match i.width_signed with
     | None -> i.value |> format_bigint |> box 
     | Some (width,signed) -> seq 
                                (seq (width |> string_of_int |> text) 
                                   (text (if signed then "s" else "w"))) 
                                (i.value |> format_bigint) |> box) 
end

module P4String = struct 
  let format_t e = seq ("\"" |> text) (seq (e |> snd |> text) ("\"" |> text)) 
end

module P4Word = struct 
  let format_t e =  e |> snd |> text
end

let name_format_t (name: Types.name) =
  match name with
  | BareName str -> P4Word.format_t str
  | QualifiedName ([], str) -> seq (text ".") (P4Word.format_t str)
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
      seq (format_t x.array) (seq (text "[") 
                                (seq (format_t x.index) (text "]"))) |> box ~indent:2
    | BitStringAccess x -> 
      seq (format_t x.bits) (seq (text "[") 
                               (seq (seq (format_t x.hi) (seq (text ":") 
                                                            (format_t x.lo))) 
                                  (text "]"))) |> box ~indent:2
    | List x -> seq (text "{") 
                  (seq (format_list_sep format_t ", " x.values) (text "}")) 
                |> box ~indent:2 
    | Record x -> seq (text "{") 
                    (seq (format_list_sep KeyValue.format_t ", " x.entries) 
                       (text "}")) 
                  |> box ~indent:2
    | UnaryOp x -> 
      let uop = match (snd x.op) with
        | Not -> "!"
        | BitNot -> "~"
        | UMinus -> "-"
      in (seq (uop |> text) (format_t x.arg)) 
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
      in (seq (format_t (fst x.args)) 
            (seq (bop |> text) 
               (format_t (snd x.args))))
         |> hbox
    | Cast x -> 
      seq ("(" |> text) 
        (seq (Type.format_t x.typ) 
           (seq (") " |> text) 
              ((format_t x.expr))))
      |> hbox 
    | TypeMember x -> 
      seq (name_format_t x.typ) 
        (seq ("." |> text) 
           (x.name |> snd |> text)) |> box ~indent:2
    | ErrorMember x -> x |> snd |> text 
    | ExpressionMember x -> seq (format_t x.expr) 
                              (seq ("." |> text) 
                                 (x.name |> snd |> text)) |> box ~indent:2
    | Ternary x ->
      seq ("(" |> text) 
        (seq (format_t x.cond) 
           (seq space (seq ("?" |> text) 
                         (seq space 
                            (seq (format_t x.tru) 
                               (seq space (seq (":" |> text) 
                                             (seq space (seq 
                                                           (format_t x.fls) 
                                                           (")" |> text)))))))))) 
      |> box ~indent:2
    | FunctionCall x ->
      seq (format_t x.func) 
        (seq (Type.format_typ_args x.type_args) 
           (seq ("(" |> text) 
              (seq (format_list_sep Argument.format_t ", " x.args) 
                 (")" |> text)))) |> box ~indent:2
    | NamelessInstantiation x ->
      seq (Type.format_t x.typ) 
        (seq ("(" |> text) 
           (seq (format_list_sep Argument.format_t ", " x.args) 
              (")" |> text))) |> box ~indent:2
    | Mask x ->
      seq (format_t x.expr) (
        seq space (seq ("&&&" |> text) 
                     (seq space (format_t x.mask)))) |> box ~indent:2
    | Range x -> 
      seq (format_t x.lo) 
        (seq space (seq (".." |> text) 
                      (seq space (format_t x.hi))))
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
      seq (format_switch_label (snd label)) 
        (seq (": " |> text) (seq (Block.format_t code) ("\n}" |> text)))
    | FallThrough { label } ->
      seq (format_switch_label (snd label)) (":" |> text)

  let block_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      seq ("else " |> text) (seq (Block.format_t fls_block) ("\n}" |> text))
    | Some sfls -> 
      seq ("\nelse" |> text) (seq space (Statement.format_t sfls)) |> box ~indent:2

  let wc_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      seq ("\n" |> text) 
        (seq (box ~indent:2
                (seq ("else " |> text) 
                   (Block.format_t fls_block))) 
           ("\n}" |> text))
    | Some sfls -> 
      seq ("\n" |> text) 
        (box ~indent:2 (seq ("else" |> text) 
                          (seq ("\n" |> text) (Statement.format_t sfls)))) 

  let rec format_t (e:t) =
    match snd e with
    | MethodCall { func; type_args; args } ->
      (seq (Expression.format_t func) 
         (seq (Type.format_typ_args type_args) 
            (seq ("(" |> text) (box (seq (Argument.format_ts args) 
                                       (seq (")" |> text) (";" |> text))))))) |> hvbox
    | Assignment { lhs; rhs } -> 
      seq (Expression.format_t lhs) 
        (seq space (seq ("=" |> text) 
                      (seq space (seq (Expression.format_t rhs) 
                                    (";" |> text))))) |> box
    | DirectApplication { typ; args } ->
      seq (Type.format_t typ) (seq (".apply(" |> text) 
                                 (seq (Argument.format_ts args) 
                                    (");" |> text))) |> hvbox 
    | Conditional { cond; tru; fls } ->
      let remainder = match snd tru with 
        | BlockStatement { block=tru_block } -> 
          seq (tru_block |> Block.format_t) 
            (seq ("\n}" |> text) (block_fls fls))
        | _ -> seq ("\n" |> text) (seq (format_t tru) (wc_fls fls))
      in seq ("if" |> text) 
        (seq space (seq ("(" |> text) 
                      (seq (Expression.format_t cond) 
                         (seq (")" |> text) (seq space remainder))))) |> box ~indent:2
    | BlockStatement { block } ->
      seq (block |> Block.format_t |> box ~indent:2) ("\n}" |> text)
    | Exit -> text "exit;"
    | EmptyStatement -> text ";"
    | Return { expr = None } -> text "return;"
    | Return { expr = Some sexpr } ->
      seq ("return" |> text) 
        (seq space (seq (Expression.format_t sexpr) 
                      (";" |> text))) |> hvbox 
    | Switch { expr; cases } -> 
      seq (hvbox (seq ("switch" |> text) 
                    (seq space 
                       (seq ("(" |> text) 
                          (seq (box (Expression.format_t expr)) 
                             (seq (")" |> text) 
                                (seq space (seq ("{\n" |> text) 
                                              (format_list_nl format_switch_case cases))))))))) 
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
      seq (Annotation.format_ts annotations) 
        (seq ("{\n" |> text) 
           (format_list_nl Statement.format_t statements))
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
      seq (x.key |> snd |> text) 
        (seq ("=" |> text) 
           (Expression.format_t x.value)) |> box ~indent:2
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
    | IntType x -> seq ("int" |> text) (seq ("<" |> text) (seq ( Expression.format_t x) (">" |> text))) |> box 
    | BitType e -> 
      begin match snd e with 
        | P4.Expression.Int _  -> 
          seq ("bit<" |> text) (seq (Expression.format_t e) (">" |> text)) |> box ~indent:2
        | _ -> 
          seq ("bit<(" |> text) (seq (Expression.format_t e) (")>" |> text)) |> box ~indent:2
      end
    | VarBit x ->
      seq ("varbit" |> text) 
        (seq space (seq ("<" |> text) 
                      (seq ( Expression.format_t x) 
                         (">" |> text)))) |> box ~indent:2
    | TypeName (BareName x) -> x |> snd |> text |> box ~indent:2
    | TypeName (QualifiedName ([], x)) ->
      seq ("." |> text) (x |> snd |> text) |> box ~indent:2
    | TypeName _ -> failwith "unimplemented" 
    | SpecializedType x -> 
      seq (format_t x.base) (seq ("<" |> text) 
                               (seq (format_list_sep format_t ", " x.args) 
                                  (">" |> text))) |> box~indent:2
    | HeaderStack x -> seq (format_t x.header) 
                         (seq ("[" |> text)
                            (seq (Expression.format_t x.size) 
                               ("]" |> text))) |> box ~indent:2  
    | Tuple x -> seq ("tuple<" |> text) 
                   (seq (format_list_sep format_t ", " x) 
                      (">" |> text)) |> box ~indent:2
    | String -> text "string"      
    | Void -> text "void"
    | DontCare -> text "_"

  let format_typ_args l =
    if List.length l = 0 then nop 
    else
      seq ("<" |> text) (seq (format_list_sep format_t ", " l) (">" |> text))

  let format_type_params l =
    if  List.length l = 0 then nop 
    else
      seq ("<" |> text) (seq (format_list_sep P4Word.format_t ", " l) (">" |> text))
end

and KeyValue : sig 
  val format_t : P4.KeyValue.t -> _ Pp.t
end = struct
  open P4.KeyValue
  let format_t kv = 
    match snd kv with 
    | { key; value } -> 
      (seq (P4Word.format_t key) 
         (seq space (seq ("=" |> text) (seq space (Expression.format_t value))))) |> box ~indent:2
end

and Annotation : sig
  val format_t : P4.Annotation.t -> _ Pp.t
  val format_ts : P4.Annotation.t list -> _ Pp.t
end = struct
  open P4.Annotation
  let format_body body = 
    match snd body with 
    | Empty -> nop 
    | Unparsed strings -> let contents = match strings with 
        | [] -> nop
        | h::t -> format_list_sep P4Word.format_t " " strings |> box 
      in 
      seq ("(" |> text) 
        (seq contents (")" |> text))
    | Expression exprs -> 
      seq ("[" |> text) 
        (seq (format_list_sep Expression.format_t ", " exprs) 
           ("]" |> text))
    | KeyValue kvs -> 
      seq ("[" |> text) 
        (seq (format_list_sep KeyValue.format_t ", " kvs) 
           ("]" |> text)) |> hovbox ~indent:2

  let format_t e =
    match snd e with 
    | { name; body } -> 
      seq ("@" |> text) (seq (P4Word.format_t name) 
                           (format_body body)) |> box 

  let format_ts l =
    match l with
    | [] -> nop 
    | _ :: _ -> seq (format_list_nl format_t l) ("\n" |> text)
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
  let format_t e =
    let p = snd e in
    seq (Annotation.format_ts p.annotations) 
      (box ~indent:2 (seq ((format_option Direction.format_t) p.direction) 
                        (seq ((match p.direction with None -> nop | Some _ -> space)) 
                             (seq (Type.format_t p.typ) 
                                (seq space 
                                   (seq (p.variable |> snd |> text) 
                                      ((format_option
                                          (fun e -> seq ("=" |> text) 
                                              (seq space (Expression.format_t e))))
                                         p.opt_value)))))))

  let format_params l = format_list_sep format_t ", " l 

  let format_constructor_params l =
    match l with
    | [] -> nop
    | _ :: _ -> seq ("(" |> text) (seq (box ~indent:2 (format_list_sep format_t ", " l)) 
                                     (")" |> text))
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
    | _ -> box ~indent:2 (seq ("(" |> text) 
                            (seq (box (format_list_sep format_t ", " l)) 
                               (")" |> text)))
end

and Parser : sig
  val format_state : P4.Parser.state -> _ Pp.t
  val format_states : P4.Parser.state list -> _ Pp.t
end = struct
  open P4.Parser

  let format_case e =
    match snd e with
    | { matches; next } ->
      seq (Match.format_ts matches) 
        (seq (":" |> text) 
           (seq space (seq (P4Word.format_t next) 
                         (";" |> text))))

  let format_transition e =
    match snd e with
    | Direct { next } -> 
      seq ("transition" |> text) 
        (seq space (seq (P4Word.format_t next) 
                      (";" |> text)))
    | Select { exprs; cases } ->
      seq (box ~indent:2 
             (seq ("transition" |> text) 
                (seq space 
                   (seq ("select(" |> text)
                      (seq (format_list_sep Expression.format_t ", " exprs) 
                         (seq (")" |> text) 
                            (begin match cases with
                               | [] -> " {" |> text
                               | _ -> seq (" {\n" |> text) 
                                        (format_list_nl format_case cases) end)))))))
        ("\n}" |> text)

  let format_state e =
    match snd e with
    | { annotations; name; statements; transition } -> 
      seq (Annotation.format_ts annotations)
        (seq (box ~indent:2 (seq ("state" |> text)
                               (seq space 
                                  (seq (P4Word.format_t name)
                                     (seq space 
                                        (seq ("{\n" |> text) 
                                           (seq (format_list_nl Statement.format_t statements)
                                              (seq (match statements with 
                                                   | [] -> nop 
                                                   | _ :: _ -> text "\n")
                                                  (format_transition transition))))))))) 
           ("\n}" |> text))

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
      box ~indent:2 (seq (Expression.format_t key) 
                       (seq (":" |> text) 
                          (seq space 
                             (seq (P4Word.format_t match_kind) 
                                (seq (Annotation.format_ts annotations) 
                                   (";" |> text))))))

  let format_action_ref e = 
    match snd e with 
    | { annotations; name; args = [] } ->
      seq (Annotation.format_ts annotations) 
        (name |> name_format_t |> box ~indent:2)
    | { annotations; name; args } ->
      seq (Annotation.format_ts annotations) 
        (box ~indent:2 (seq (name_format_t name) 
                          (seq ("(" |> text) 
                             (seq (box (Argument.format_ts args))  
                                (")" |> text)))))

  let format_entry e =
    match snd e with
    | { annotations; matches; action } ->
      seq (box ~indent:2 (seq (Match.format_ts matches) 
                            (seq (":" |> text) 
                               (seq space (format_action_ref action)))))
        (seq (Annotation.format_ts annotations)
           (";" |> text))

  let format_property e = 
    match snd e with 
    | Key  { keys } ->
      seq (box ~indent:2 (seq ("key" |> text) 
                            (seq space 
                               (seq ("=" |> text) 
                                  (seq space 
                                     (seq ("{\n" |> text) 
                                        (format_list_nl format_key keys)))))))
        ("\n}" |> text)
    | Actions { actions } ->
      seq (box ~indent:2 (seq ("actions" |> text) 
                            (seq space 
                               (seq ("=" |> text) 
                                  (seq space 
                                     (seq ("{\n" |> text) 
                                        (seq (format_list_sep_nl format_action_ref ";" actions)
                                           (begin match actions with
                                              | [] -> nop
                                              | _ -> ";" |> text end))))))))
        ("\n}" |> text)
    | Entries { entries } ->
      seq (box ~indent:2 (seq ("const entries" |> text) 
                            (seq space 
                               (seq ("=" |> text) 
                                  (seq space 
                                     (seq ("{\n" |> text) 
                                        (format_list_nl format_entry entries)))))))
        ("\n}" |> text)
    | Custom { annotations; const; name; value } ->
      seq (Annotation.format_ts annotations) 
        (box ~indent:2 (seq ((if const then "const " else "") |> text) 
                          (seq (P4Word.format_t name)
                             (seq space 
                                (seq ("=" |> text)
                                   (seq space 
                                      (seq (Expression.format_t value) 
                                         (";" |> text))))))))
end 

and MethodPrototype : sig
  val format_t : P4.MethodPrototype.t -> _ Pp.t
end = struct
  open P4.MethodPrototype
  let format_t e =
    match snd e with
    | Constructor { annotations; name; params } ->
      seq (Annotation.format_ts annotations) 
        (box ~indent:2 (seq (P4Word.format_t name) 
                          (seq (" (" |> text)
                             (seq (box (Parameter.format_params params))
                                (");" |> text)))))
    | Method { annotations; return; name; type_params; params } ->
      seq (Annotation.format_ts annotations) 
        (box ~indent:2 (seq (Type.format_t return) 
                          (seq space 
                             (seq ( P4Word.format_t name)
                                (seq (Type.format_type_params type_params)
                                   (seq (" (" |> text)
                                      (seq (box (Parameter.format_params params)) 
                                         (");" |> text))))))))
    | AbstractMethod { annotations; return; name; type_params; params } -> 
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("abstract" |> text)
                          (seq space 
                             (seq (Type.format_t return)
                                (seq space 
                                   (seq (P4Word.format_t name)
                                      (seq (Type.format_type_params type_params)
                                         (seq (" (" |> text)
                                            (seq (box (Parameter.format_params params))
                                               (");" |> text))))))))))
end

and Declaration : sig
  val format_t : P4.Declaration.t -> _ Pp.t
end = struct
  open P4.Declaration

  let format_field f =
    match snd f with
    | { annotations; typ; name } ->
      seq (annotations |> Annotation.format_ts |> box)
        (box ~indent:2 (seq (Type.format_t typ) 
                          (seq space 
                             (seq (P4Word.format_t name)
                                (";" |> text)))))

  let format_typ_or_decl td =
    match td with
    | Left(typ) ->
      Type.format_t typ
    | Right(decl) ->
      Declaration.format_t decl


  let rec dec_help locals = 
    if not (List.length locals = 0) then 
      seq (format_list_sep format_t "\n" locals) ("\n" |> text)
    else nop 

  and format_t e = 
    match snd e with 
    | Constant { annotations; typ; name; value } -> 
      (seq (Annotation.format_ts annotations)
         (box ~indent:2 (seq ("const" |> text)
                           (seq space 
                              (seq (Type.format_t typ) 
                                 (seq space 
                                    (seq (name |> snd |> text)
                                       (seq space 
                                          (seq ("=" |> text)
                                             (seq space 
                                                (seq (Expression.format_t value)
                                                   (";" |> text))))))))))))
    | Action { annotations; name; params; body } ->
      seq (Annotation.format_ts annotations)
        (seq (box ~indent:2
                (seq ("action" |> text)
                   (seq space
                      (seq (name |> snd |> text) 
                         (seq ("(" |> text)
                            (seq (box (Parameter.format_params params))
                               (seq (") " |> text)
                                  (Block.format_t body)))))))) ("\n}" |> text))
    | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
      seq (Annotation.format_ts annotations)
        (seq 
           (box ~indent:2
              (seq ("control" |> text)
                 (seq space 
                    (seq (name |> snd |> text)
                       (seq (Type.format_type_params type_params)
                          (seq ("(" |> text)
                             (seq (box (Parameter.format_params params))
                                (seq (")" |> text)
                                   (seq (Parameter.format_constructor_params constructor_params)
                                      (seq (" {\n" |> text)
                                         (seq (dec_help locals) 
                                            (seq (box ~indent: 2 (seq ("apply " |> text)
                                                                    (Block.format_t apply))) 
                                               ("\n}" |> text)))))))))))))
           ("\n}" |> text))
    | Parser { annotations; name; type_params; params; constructor_params; locals; states } ->
      seq 
        (box ~indent:2 
           (seq 
              (seq (Annotation.format_ts annotations) 
                 (seq ("parser" |> text)
                    (seq space 
                       (seq (name |> snd |> text) 
                          (seq (Type.format_type_params type_params)
                             (seq (" (" |> text)
                                (seq (box (Parameter.format_params params))
                                   (seq (")" |> text)
                                      (seq (Parameter.format_constructor_params constructor_params)
                                         (" {\n" |> text))))))))))
              (seq (dec_help locals) (Parser.format_states states) )))
        ("\n}\n" |> text)
    | Instantiation { annotations; typ; args; name; init=None } -> 
      seq (Annotation.format_ts annotations) 
        (box ~indent:2 (seq (Type.format_t typ) 
                          (seq ("(" |> text)
                             (seq (box (Argument.format_ts args))
                                (seq (")" |> text)
                                   (seq space 
                                      (seq (P4Word.format_t name)
                                         (";" |> text))))))))
    | Instantiation { annotations; typ; args; name; init=Some block } -> 
      seq (seq (Annotation.format_ts annotations)
             (box ~indent: 2
                (seq (Type.format_t typ)
                   (seq ("(" |> text)
                      (seq (box (Argument.format_ts args)) 
                         (seq (")" |> text)
                            (seq space
                               (seq (P4Word.format_t name)
                                  (seq space
                                     (seq ("= " |> text)
                                        (Block.format_t block)))))))))))
        ("\n};" |> text)
    | Table { annotations; name; properties } -> 
      seq 
        (box ~indent:2 (seq (seq (Annotation.format_ts annotations)
                               (seq ("table" |> text)
                                  (seq space 
                                     (seq (P4Word.format_t name)
                                        (" {\n" |> text)))))
                          (format_list_nl Table.format_property properties))) 
        ("\n}" |> text)  
    | Variable { annotations; typ; name; init = None } ->
      seq (Annotation.format_ts annotations)    
        (box ~indent:2 (seq (Type.format_t typ) 
                          (seq space 
                             (seq (P4Word.format_t name)
                                (";" |> text)))))      
    | Variable { annotations; typ; name; init = Some sinit } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq (Type.format_t typ)
                          (seq space 
                             (seq (P4Word.format_t name)
                                (seq space 
                                   (seq ("=" |> text)
                                      (seq space 
                                         (seq (Expression.format_t sinit)
                                            (";" |> text)))))))))                   
    | ExternFunction { annotations; return; name; type_params; params } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("extern" |> text)
                          (seq space
                             (seq (Type.format_t return)
                                (seq space
                                   (seq (P4Word.format_t name)
                                      (seq (Type.format_type_params type_params)
                                         (seq (" (" |> text)
                                            (seq (box (Parameter.format_params params))
                                               (");" |> text))))))))))
    | Function { return; name; type_params; params; body } ->
      seq (box ~indent:2 (seq (Type.format_t return)
                            (seq space 
                               (seq (P4Word.format_t name)
                                  (seq (Type.format_type_params type_params)
                                     (seq (" (" |> text)
                                        (seq (box (Parameter.format_params params))
                                           (seq (") " |> text)
                                              (Block.format_t body)))))))))
        ("\n}" |> text)
    | ValueSet { annotations; typ; size; name } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("value_set<" |> text)
                          (seq (Type.format_t typ)
                             (seq (">(" |> text)
                                (seq (box (Expression.format_t size))
                                   (seq (")" |> text)
                                      (seq space
                                         (seq (P4Word.format_t name)
                                            (";" |> text)))))))))
    | TypeDef { annotations; name; typ_or_decl } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("typedef" |> text)
                          (seq space 
                             (seq (format_typ_or_decl typ_or_decl)
                                (seq space
                                   (seq (name |> snd |> text)
                                      (";" |> text)))))))
    | ControlType { annotations; name; type_params; params } -> 
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("control" |> text)
                          (seq space 
                             (seq (name |> snd |> text)
                                (seq (Type.format_type_params type_params)
                                   (seq (" (" |> text)
                                      (seq (box (format_list_sep Parameter.format_t ", " params))
                                         (");" |> text))))))))
    | ParserType { annotations; name; type_params; params } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 
           (seq ("parser" |> text)
              (seq space 
                 (seq (name |> snd |> text)
                    (seq (Type.format_type_params type_params)
                       (seq (" (" |> text)
                          (seq (box (format_list_sep Parameter.format_t ", " params))
                             (");" |> text)))))))) 
    | PackageType { annotations; name; type_params; params } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 
           (seq ("package" |> text)
              (seq space 
                 (seq (name |> snd |> text)
                    (seq (Type.format_type_params type_params)
                       (seq (" (" |> text)
                          (seq (box (format_list_sep Parameter.format_t ", " params))
                             (");" |> text)))))))) 
    | Struct { annotations; name; fields } -> 
      seq (Annotation.format_ts annotations)
        (seq (box ~indent:2 (seq ("struct" |> text)
                               (seq space 
                                  (seq (P4Word.format_t name)
                                     (begin match fields with
                                        | [] -> " {" |> text
                                        | _ -> seq (" {\n" |> text) (format_list_nl format_field fields) end)))))
           ("\n}" |> text))
    | MatchKind { members=[] } ->
      "match_kind {\n}" |> text |> box
    | MatchKind { members } ->
      seq (box ~indent:2 (seq ("match_kind" |> text)
                            (seq space
                               (seq ("{\n" |> text)
                                  (format_list_sep_nl P4Word.format_t ", " members)))))
        ("\n}" |> text)
    | Error { members=[] } ->
      box ("error {\n}" |> text)
    | Error { members } ->
      seq (box ~indent:2 (seq ("error {" |> verbatim)
                            (seq newline 
                               (format_list_sep_nl P4Word.format_t ", " members))))
        ("\n}" |> text)
    | Enum { annotations; name; members=[] } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 (seq ("enum" |> text)
                          (seq space 
                             (seq (P4Word.format_t name)
                                (seq space 
                                   ("{\n}" |> text))))))
    | Enum { annotations; name; members } ->
      seq 
        (seq (Annotation.format_ts annotations)
           (box ~indent:2
              (seq ("enum" |> text)
                 (seq space 
                    (seq (P4Word.format_t name)
                       (seq space 
                          (seq ("{\n" |> text)
                             (format_list_sep_nl P4Word.format_t ", " members))))))))
        ("\n}" |> text)
    | SerializableEnum { annotations; typ; name; members=[] } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2 
           (seq ("enum" |> text)
              (seq space 
                 (seq (Type.format_t typ)
                    (seq space
                       (seq (P4Word.format_t name)
                          (seq space 
                             (seq ("{" |> text)
                                (seq newline 
                                   ("}" |> text))))))))))
    | SerializableEnum { annotations; typ; name; members } ->
      let format_member (field,init) =
        seq (P4Word.format_t field)
          (seq space 
             (seq ("=" |> text)
                (seq space
                   (Expression.format_t init)))) in 
      seq (seq (Annotation.format_ts annotations)
             (box ~indent: 2
                (seq ("enum" |> text)
                   (seq space
                      (seq (Type.format_t typ)
                         (seq space
                            (seq (P4Word.format_t name)
                               (seq (" {\n" |> text)
                                  (format_list_sep_nl format_member ", " members)))))))))
        ("\n}" |> text)   
    | ExternObject { annotations; name; type_params; methods = [] } ->
      seq (Annotation.format_ts annotations)
        (box ~indent:2
           (seq ("extern" |> text)
              (seq space 
                 (seq (P4Word.format_t name)
                    (seq space 
                       (seq (Type.format_type_params type_params)
                          (seq space 
                             (seq ("{" |> text)
                                (seq newline 
                                   ("}" |> text)))))))))) 
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
      seq (Annotation.format_ts annotations)
        (seq (box ~indent:2 
                (seq ("header" |> text)
                   (seq space 
                      (seq (P4Word.format_t name)
                         (begin match fields with
                            | [] -> " {" |> text
                            | _ -> seq (" {\n" |> text) (format_list_nl format_field fields) end)))))
           ("\n}" |> text)) 
    | HeaderUnion { annotations; name; fields } ->
      seq (Annotation.format_ts annotations)
        (seq (box ~indent:2 (seq ("header_union" |> text)
                               (seq space 
                                  (seq (P4Word.format_t name)
                                     (begin match fields with
                                        | [] -> " {" |> text
                                        | _ -> seq (" {\n" |> text) (format_list_nl format_field fields) end)))))
           ("\n}" |> text))
    | NewType { annotations; name; typ_or_decl } ->
      box ~indent:2 (seq (Annotation.format_ts annotations)
                       (seq ("type" |> text)
                          (seq space 
                             (seq (format_typ_or_decl typ_or_decl)
                                (seq space 
                                   (seq (name |> snd |> text)
                                      (";" |> text)))))))
end 

let format_program p =
  match p with
  | P4.Program(ds) ->
    box (seq (format_list_nl Declaration.format_t ds)
           ("\n" |> text))

