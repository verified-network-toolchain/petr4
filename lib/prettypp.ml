open Core_kernel
open Pp
open StdLabels
open List 
open Util
module P4 = Types 

let print pp = Format.printf "%a" Pp.to_fmt pp

let to_string pp : string =
  Format.fprintf Format.str_formatter "%a" Pp.to_fmt pp;
  Format.flush_str_formatter ()

let format_list_sep f sep l = 
  Pp.concat_map ~sep:("," |> text) l ~f:f

let format_list_nl f l = 
  Pp.concat_map ~sep:("\n" |> text) l ~f:f

let format_option f o =
  match o with
  | None -> nop 
  | Some x -> f x 

let format_list_term f term l =
  (* let g x =
     seq (f x)
      (seq (term |> text) ("," |> text)) in
     List.iter l ~f:g *)
  failwith "what's the diff b/w this and format_list_sep"

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
  let format_t e = e |> snd |> text
end

let name_format_t (name: Types.name) =
  match name with
  | BareName str -> P4String.format_t str
  | QualifiedName ([], str) -> seq (text ".") (P4String.format_t str)
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
                                (seq (format_t x.index) (text "]"))) |> box 
    | BitStringAccess x -> 
      seq (format_t x.bits) (seq (text "[") 
                               (seq (seq (format_t x.hi) (seq (text ":") 
                                                            (format_t x.lo))) 
                                  (text "]"))) |> box
    | List x -> seq (text "{") 
                  (seq (format_list_sep format_t "," x.values) (text "}")) 
                |> box 
    | Record x -> seq (text "{") 
                    (seq (format_list_sep KeyValue.format_t "," x.entries) 
                       (text "}")) 
                  |> box 
    | UnaryOp x -> 
      let uop = match (snd x.op) with
        | Not -> "!"
        | BitNot -> "~"
        | UMinus -> "-"
      in seq ("(" |> text) (seq (uop |> text) 
                              (seq (format_t x.arg) (")" |> text)))
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
        | BitAnd -> "&"
        | BitXor -> "^"
        | BitOr -> "|"
        | PlusPlus -> "++"
        | And -> "&&"
        | Or -> "||"
      in seq ("(" |> text) (seq (format_t (fst x.args)) 
                              (seq space (seq (bop |> text) 
                                            (seq space (seq (format_t (snd x.args)) 
                                                          (")" |> text)))))) 
         |> box
    | Cast x -> 
      seq ("(" |> text) 
        (seq (Type.format_t x.typ) 
           (seq (")" |> text) 
              (seq ("(" |> text) 
                 (seq (format_t x.expr) (")" |> text)))))
      |> box 
    | TypeMember x -> 
      seq (name_format_t x.typ) 
        (seq ("." |> text) 
           (x.name |> snd |> text)) |> box 
    | ErrorMember x -> 
      failwith "figure out how to pring errors? maybe use color"
    | ExpressionMember x -> seq (format_t x.expr) 
                              (seq ("." |> text) 
                                 (x.name |> snd |> text)) |> box 
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
      |> box 
    | FunctionCall x ->
      seq (format_t x.func) 
        (seq (Type.format_typ_args x.type_args) 
           (seq ("(" |> text) 
              (seq (format_list_sep Argument.format_t "," x.args) 
                 (")" |> text)))) |> box 
    | NamelessInstantiation x ->
      seq (Type.format_t x.typ) 
        (seq ("(" |> text) 
           (seq (format_list_sep Argument.format_t "," x.args) 
              (")" |> text))) |> box 
    | Mask x ->
      seq (format_t x.expr) (
        seq space (seq ("&&&" |> text) 
                     (seq space (format_t x.mask)))) |> box 
    | Range x -> 
      seq (format_t x.lo) 
        (seq space (seq (".." |> text) 
                      (seq space (format_t x.hi))))
      |> box 
end 

and Statement : sig 
  val format_t : P4.Statement.t -> _ Pp.t
end = struct 
  open P4.Statement 

  let format_switch_label sl =
    match sl with
    | Default -> text "default"
    | Name(sl) -> sl |> P4String.format_t |> box 

  let format_switch_case sc =
    match snd sc with
    | Action { label; code } ->
      seq (format_switch_label (snd label)) 
        (seq (":" |> text) (seq space (Block.format_t code)))
    | FallThrough { label } ->
      seq (format_switch_label (snd label)) (":" |> text)

  let block_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      seq ("else" |> text) (seq space (Block.format_t fls_block))
    | Some sfls -> 
      seq ("\nelse" |> text) (seq space (Statement.format_t sfls)) |> box 

  let wc_fls fls = 
    match fls with 
    | None -> nop 
    | Some (_, BlockStatement { block=fls_block }) ->
      seq ("\n" |> text) 
        (box (seq ("else" |> text) 
                (seq space (Block.format_t fls_block)))) 
    | Some sfls -> 
      seq ("\n" |> text) 
        (box (seq ("else" |> text) 
                (seq ("\n" |> text) (Statement.format_t sfls)))) 

  let rec format_t (e:t) =
    match snd e with
    | MethodCall { func; type_args; args } ->
      seq (Expression.format_t func) 
        (seq (Type.format_typ_args type_args) 
           (seq ("(" |> text) (seq (Argument.format_ts args) 
                                 (seq (")" |> text) (";" |> text))))) |> box
    | Assignment { lhs; rhs } -> 
      seq (Expression.format_t lhs) 
        (seq space (seq ("=" |> text) 
                      (seq space (seq (Expression.format_t rhs) 
                                    (";" |> text))))) |> box
    | DirectApplication { typ; args } ->
      seq (Type.format_t typ) (seq (".apply(" |> text) 
                                 (seq (Argument.format_ts args) 
                                    (");" |> text))) |> box 
    | Conditional { cond; tru; fls } ->
      let remainder = match snd tru with 
        | BlockStatement { block=tru_block } -> seq (tru_block |> Block.format_t) 
                                                  (block_fls fls)
        | _ -> seq ("\n" |> text) (seq (format_t tru) (wc_fls fls))
      in seq ("if" |> text) 
        (seq space (seq ("(" |> text) 
                      (seq (Expression.format_t cond) 
                         (seq (")" |> text) (seq space remainder))))) |> box
    | BlockStatement { block } ->
      block |> Block.format_t |> box
    | Exit -> text "exit;"
    | EmptyStatement -> text ";"
    | Return { expr = None } -> text "return;"
    | Return { expr = Some sexpr } ->
      seq ("return" |> text) 
        (seq space (seq (Expression.format_t sexpr) 
                      (";" |> text))) |> box 
    | Switch { expr; cases } -> 
      seq (box (seq ("switch" |> text) 
                  (seq space 
                     (seq ("(" |> text) 
                        (seq (Expression.format_t expr) 
                           (seq (")" |> text) 
                              (seq space (seq ("{" |> text) 
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
    | { annotations=[]; statements=[] } -> "{ }" |> text |> box 
    | { annotations; statements } ->
      seq (box 
             (seq (Annotation.format_ts annotations) 
                (seq ("{\n" |> text) 
                   (format_list_nl Statement.format_t statements)))) 
        ("\n}" |> text)
end

and Argument : sig
  val format_t : P4.Argument.t -> _ Pp.t
  val format_ts : P4.Argument.t list -> _ Pp.t
end = struct
  open P4.Argument
  let format_t e =
    match snd e with
    | Expression x ->
      x.value |> Expression.format_t |> box 
    | KeyValue x ->
      seq (x.key |> snd |> text) 
        (seq ("=" |> text) 
           (Expression.format_t x.value)) |> box 
    | Missing -> text "_"
  let format_ts l =
    format_list_sep format_t "," l |> box 
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
          seq ("[bit" |> text) (seq (Expression.format_t e) (">" |> text)) |> box 
        | _ -> 
          seq ("[bit(" |> text) (seq (Expression.format_t e) (")>" |> text)) |> box
      end
    | VarBit x ->
      seq ("varbit" |> text) 
        (seq space (seq ("<" |> text) 
                      (seq ( Expression.format_t x) 
                         (">" |> text)))) |> box 
    | TypeName (BareName x) -> x |> snd |> text |> box 
    | TypeName (QualifiedName ([], x)) ->
      seq ("." |> text) (x |> snd |> text) |> box 
    | TypeName _ -> failwith "unimplemented" 
    | SpecializedType x -> 
      seq (format_t x.base) (seq ("<" |> text) 
                               (seq (format_list_sep format_t "," x.args) 
                                  (">" |> text))) |> box
    | HeaderStack x -> seq (format_t x.header) 
                         (seq ("[" |> text)
                            (seq (Expression.format_t x.size) 
                               ("]" |> text))) |> box  
    | Tuple x -> seq ("tuple<" |> text) 
                   (seq (format_list_sep format_t "," x) 
                      (">" |> text)) |> box 
    | String -> text "string"      
    | Void -> text "void"
    | DontCare -> text "_"

  let format_typ_args l =
    if List.length l = 0 then nop 
    else
      seq ("<" |> text) (seq (format_list_sep format_t "," l) (">" |> text))

  let format_type_params l =
    if  List.length l = 0 then nop 
    else
      seq ("<" |> text) (seq (format_list_sep P4String.format_t "," l) (">" |> text))
end

and KeyValue : sig 
  val format_t : P4.KeyValue.t -> _ Pp.t
end = struct
  open P4.KeyValue
  let format_t kv = 
    match snd kv with 
    | { key; value } -> 
      seq (P4String.format_t key) 
        (seq space (seq ("=" |> text) (seq space (Expression.format_t value))))
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
      seq ("(" |> text) 
        (seq (format_list_sep P4String.format_t " " strings) 
           (")" |> text))
    | Expression exprs -> 
      seq ("[" |> text) 
        (seq (format_list_sep Expression.format_t "," exprs) 
           ("]" |> text))
    | KeyValue kvs -> 
      seq ("{" |> text) 
        (seq (format_list_sep KeyValue.format_t "," kvs) 
           ("}" |> text))

  let format_t e =
    match snd e with 
    | { name; body } -> 
      seq ("@" |> text) (seq (P4String.format_t name) 
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
      (box (seq ((format_option Direction.format_t) p.direction) 
              (seq ((match p.direction with None -> nop | Some _ -> space)) 
                   (seq (Type.format_t p.typ) 
                      (seq (p.variable |> snd |> text) 
                         ((format_option
                             (fun e -> seq ("=" |> text) 
                                 (seq space (Expression.format_t e))))
                            p.opt_value)))))) |> box 

  let format_params l = format_list_sep format_t "," l |> box 

  let format_constructor_params l =
    match l with
    | [] -> nop 
    | _ :: _ -> seq ("(" |> text) (seq (box (format_list_sep format_t "," l)) 
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
    | _ -> box (seq ("(" |> text) 
                  (seq (format_list_sep format_t "," l) 
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
           (seq space (seq (P4String.format_t next) 
                         (";" |> text))))

  let format_transition e =
    match snd e with
    | Direct { next } -> 
      seq ("transition" |> text) 
        (seq space (seq (P4String.format_t next) 
                      (";" |> text)))
    | Select { exprs; cases } ->
      seq (box (seq ("transition" |> text) 
                  (seq space 
                     (seq ("select(" |> text)
                        (seq (format_list_sep Expression.format_t "," exprs) 
                           (seq (")" |> text) 
                              (seq space 
                                 (seq ("{" |> text) 
                                    (format_list_nl format_case cases)))))))))
        ("\n}" |> text)

  let format_state e =
    match snd e with
    | { annotations; name; statements; transition } -> 
      seq (Annotation.format_ts annotations)
        (seq (box (seq ("state" |> text)
                     (seq space 
                        (seq (format_list_nl Statement.format_t statements)
                           (seq space 
                              (seq ("{" |> text) 
                                 (seq ("\n" |> text) 
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
      box (seq (Expression.format_t key) 
             (seq space 
                (seq (":" |> text) 
                   (seq space 
                      (seq (P4String.format_t match_kind) 
                         (seq space 
                            (seq (Annotation.format_ts annotations) 
                               (";" |> text))))))))

  let format_action_ref e = 
    match snd e with 
    | { annotations; name; args = [] } ->
      seq (Annotation.format_ts annotations) 
        (name |> name_format_t |> box)
    | { annotations; name; args } ->
      seq (Annotation.format_ts annotations) 
        (box (seq (name_format_t name) 
                (seq ("(" |> text) 
                   (seq (Argument.format_ts args) 
                      (")" |> text)))))

  let format_entry e =
    match snd e with
    | { annotations; matches; action } ->
      seq (box (seq (Match.format_ts matches) 
                  (seq space 
                     (seq (":" |> text) 
                        (seq space (format_action_ref action))))))
        (seq (Annotation.format_ts annotations)
           (";" |> text))

  let format_property e = 
    match snd e with 
    | Key  { keys } ->
      seq (box (seq ("key" |> text) 
                  (seq space 
                     (seq ("=" |> text) 
                        (seq space 
                           (seq ("{\n" |> text) 
                              (format_list_nl format_key keys)))))))
        ("\n}" |> text)
    | Actions { actions } ->
      seq (box (seq ("actions" |> text) 
                  (seq space 
                     (seq ("=" |> text) 
                        (seq space 
                           (seq ("{\n" |> text) 
                              (format_list_term format_action_ref ";" actions)))))))
        ("\n}" |> text)
    | Entries { entries } ->
      seq (box (seq ("const entries" |> text) 
                  (seq space 
                     (seq ("=" |> text) 
                        (seq space 
                           (seq ("{\n" |> text) 
                              (format_list_nl format_entry entries)))))))
        ("\n}" |> text)
    | Custom { annotations; const; name; value } ->
      seq (Annotation.format_ts annotations) 
        (box (seq ((if const then "const " else "") |> text) 
                (seq (P4String.format_t name)
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
        (box (seq (P4String.format_t name) 
                (seq ("(" |> text)
                   (seq (Parameter.format_params params)
                      (");" |> text)))))
    | Method { annotations; return; name; type_params; params } ->
      box (seq (Type.format_t return) 
             (seq space 
                (seq ( P4String.format_t name)
                   (seq (Type.format_type_params type_params)
                      (seq ("(" |> text)
                         (seq (Parameter.format_params params) 
                            (");" |> text)))))))
    | AbstractMethod { annotations; return; name; type_params; params } -> 
      seq (Annotation.format_ts annotations)
        (box (seq ("abstract" |> text)
                (seq space 
                   (seq (Type.format_t return)
                      (seq space 
                         (seq (P4String.format_t name)
                            (seq (Type.format_type_params type_params)
                               (seq ("(" |> text)
                                  (seq (Parameter.format_params params)
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
        (box (seq (Type.format_t typ) 
                (seq space 
                   (seq (P4String.format_t name)
                      (";" |> text)))))

  let format_fields l =
    match l with
    | [] -> nop
    | _ :: _ ->
      seq ("{\n" |> text) 
        (seq (box (format_list_nl format_field l))
           ("\n}" |> text))

  let format_typ_or_decl td =
    match td with
    | Left(typ) ->
      Type.format_t typ
    | Right(decl) ->
      Declaration.format_t decl

  let rec dec_help locals = 
    if not (List.length locals = 0) then 
      seq (format_list_nl format_t locals) ("\n" |> text)
    else nop 

  and format_t e = 
    match snd e with 
    | Constant { annotations; typ; name; value } -> 
      box (seq (Annotation.format_ts annotations)
             (seq ("const" |> text)
                (seq space 
                   (seq (Type.format_t typ) 
                      (seq space 
                         (seq (name |> snd |> text)
                            (seq space 
                               (seq ("=" |> text)
                                  (seq space 
                                     (seq ( Expression.format_t value)
                                        (";" |> text)))))))))))
    | Action { annotations; name; params; body } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("action" |> text)
                (seq space
                   (seq (name |> snd |> text) 
                      (seq ("(" |> text)
                         (seq (box (Parameter.format_params params))
                            (seq (")" |> text)
                               (seq space (Block.format_t body)))))))))
    | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
      seq (Annotation.format_ts annotations)
        (seq ("control" |> text)
           (seq space 
              (seq (name |> snd |> text)
                 (seq (Type.format_type_params type_params)
                    (seq ("(" |> text)
                       (seq (Parameter.format_params params)
                          (seq (")" |> text)
                             (seq (Parameter.format_constructor_params constructor_params)
                                (seq ("{\n" |> text)
                                   (seq (dec_help locals) 
                                      (seq (box (seq ("apply" |> text) 
                                                   (seq space 
                                                      (Block.format_t apply)))) ("\n}" |> text))))))))))))
    | Parser { annotations; name; type_params; params; constructor_params; locals; states } ->
      seq 
        (box 
           (seq (Annotation.format_ts annotations) 
              (seq ("parser" |> text)
                 (seq space 
                    (seq (name |> snd |> text) 
                       (seq (Type.format_type_params type_params)
                          (seq ("(" |> text)
                             (seq (Parameter.format_params params)
                                (seq (")" |> text)
                                   (seq (Parameter.format_constructor_params constructor_params)
                                      (seq space 
                                         (seq ("{\n" |> text)
                                            (seq (dec_help locals)
                                               (Parser.format_states states))))))))))))))
        ("\n" |> text)
    | Instantiation { annotations; typ; args; name; init=None } -> 
      seq (Annotation.format_ts annotations) 
        (box (seq (Type.format_t typ) 
                (seq ("(" |> text)
                   (seq (Argument.format_ts args)
                      (seq (")" |> text)
                         (seq space 
                            (seq (P4String.format_t name)
                               (";" |> text))))))))
    | Instantiation { annotations; typ; args; name; init=Some block } -> 
      seq (Annotation.format_ts annotations)
        (box (seq (Type.format_t typ)
                (seq ("(" |> text)
                   (seq (Argument.format_ts args)
                      (seq (")" |> text)
                         (seq space
                            (seq (P4String.format_t name)
                               (seq space
                                  (seq ("=" |> text)
                                     (seq space
                                        (seq (Block.format_t block) 
                                           (";" |> text))))))))))))
    | Table { annotations; name; properties } -> 
      seq 
        (seq (Annotation.format_ts annotations)
           (box 
              (seq ("table" |> text)
                 (seq space 
                    (seq (P4String.format_t name)
                       (seq space
                          (seq ("{\n" |> text)
                             (format_list_nl Table.format_property properties))))))))
        ("\n}" |> text)  
    | Variable { annotations; typ; name; init = None } ->
      seq (Annotation.format_ts annotations)    
        (box (seq (Type.format_t typ) 
                (seq space 
                   (seq (P4String.format_t name)
                      (";" |> text)))))      
    | Variable { annotations; typ; name; init = Some sinit } ->
      seq (Annotation.format_ts annotations)
        (box (seq (Type.format_t typ)
                (seq space 
                   (seq (P4String.format_t name)
                      (seq space 
                         (seq ("=" |> text)
                            (seq space 
                               (seq (Expression.format_t sinit)
                                  (";" |> text)))))))))                   
    | ExternFunction { annotations; return; name; type_params; params } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("extern" |> text)
                (seq space
                   (seq (Type.format_t return)
                      (seq space
                         (seq (P4String.format_t name)
                            (seq (Type.format_type_params type_params)
                               (seq ("(" |> text)
                                  (seq (Parameter.format_params params)
                                     (");" |> text))))))))))
    | Function { return; name; type_params; params; body } ->
      box (seq (Type.format_t return)
             (seq space 
                (seq (P4String.format_t name)
                   (seq (Type.format_type_params type_params)
                      (seq ("(" |> text)
                         (seq (Parameter.format_params params)
                            (seq (")" |> text)
                               (seq space 
                                  (Block.format_t body)))))))))
    | ValueSet { annotations; typ; size; name } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("value_set<" |> text)
                (seq (Type.format_t typ)
                   (seq (">(" |> text)
                      (seq (Expression.format_t size)
                         (seq (")" |> text)
                            (seq space
                               (seq (P4String.format_t name)
                                  (";" |> text)))))))))
    | TypeDef { annotations; name; typ_or_decl } ->
      box (seq (Annotation.format_ts annotations)
             (seq ("typedef" |> text)
                (seq space 
                   (seq (format_typ_or_decl typ_or_decl)
                      (seq space
                         (seq (name |> snd |> text)
                            (";" |> text)))))))
    | ControlType { annotations; name; type_params; params } -> 
      box (seq (Annotation.format_ts annotations)
             (seq ("control" |> text)
                (seq space 
                   (seq (name |> snd |> text)
                      (seq (Type.format_type_params type_params)
                         (seq (",(" |> text)
                            (seq (box (format_list_sep Parameter.format_t "," params))
                               (");" |> text))))))))
    | ParserType { annotations; name; type_params; params } ->
      box (seq (Annotation.format_ts annotations)
             (seq ("parser" |> text)
                (seq space 
                   (seq (name |> snd |> text)
                      (seq (Type.format_type_params type_params)
                         (seq (",(" |> text)
                            (seq (box (format_list_sep Parameter.format_t "," params))
                               (");" |> text)))))))) 
    | PackageType { annotations; name; type_params; params } ->
      box (seq (Annotation.format_ts annotations)
             (seq ("package" |> text)
                (seq space 
                   (seq (name |> snd |> text)
                      (seq (Type.format_type_params type_params)
                         (seq (",(" |> text)
                            (seq (box (format_list_sep Parameter.format_t "," params))
                               (");" |> text)))))))) 
    | Struct { annotations; name; fields } ->
      seq (box (Annotation.format_ts annotations)) 
        (box 
           (seq ("struct" |> text)
              (seq space 
                 (seq (P4String.format_t name)
                    (seq space 
                       (format_fields fields))))))
    | MatchKind { members=[] } ->
      "match_kind { }" |> text |> box
    | MatchKind { members } ->
      seq (box (seq ("match_kind" |> text)
                  (seq space
                     (seq ("{\n" |> text)
                        (format_list_sep_nl P4String.format_t "," members)))))
        ("\n}" |> text)
    | Error { members=[] } ->
      box ("error { }" |> text)
    | Error { members } ->
      seq (box 
             (seq ("error" |> text)
                (seq space
                   (seq ("{\n" |> text)
                      (format_list_sep_nl P4String.format_t "," members)))))
        ("\n}" |> text)
    | Enum { annotations; name; members=[] } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("enum" |> text)
                (seq space 
                   (seq (P4String.format_t name)
                      (seq space 
                         ("{ }" |> text))))))
    | Enum { annotations; name; members } ->
      seq 
        (seq (Annotation.format_ts annotations)
           (box 
              (seq ("enum" |> text)
                 (seq space 
                    (seq (P4String.format_t name)
                       (seq space 
                          (seq ("{\n" |> text)
                             (format_list_sep_nl P4String.format_t "," members))))))))
        ("\n}" |> text)
    | SerializableEnum { annotations; typ; name; members=[] } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("enum" |> text)
                (seq space 
                   (seq (Type.format_t typ)
                      (seq space
                         (seq (P4String.format_t name)
                            (seq space 
                               (seq ("{" |> text)
                                  (seq space 
                                     ("}" |> text))))))))))
    | SerializableEnum { annotations; typ; name; members } ->
      let format_member (field,init) =
        seq (P4String.format_t field)
          (seq space 
             (seq ("=" |> text)
                (seq space
                   (Expression.format_t init)))) in 
      seq (seq (Annotation.format_ts annotations)
             (box (seq ("enum" |> text)
                     (seq space
                        (seq (Type.format_t typ)
                           (seq space
                              (seq (P4String.format_t name)
                                 (seq ("{\n" |> text)
                                    (format_list_sep_nl format_member "," members)))))))))
        ("\n}" |> text)   
    | ExternObject { annotations; name; type_params; methods = [] } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("extern" |> text)
                (seq space 
                   (seq (P4String.format_t name)
                      (seq (Type.format_type_params type_params)
                         (seq space 
                            (seq ("{" |> text)
                               (seq space 
                                  ("}" |> text)))))))))  
    | ExternObject { annotations; name; type_params; methods } ->
      seq 
        (seq (Annotation.format_ts annotations)
           (box (seq ("extern" |> text)
                   (seq space 
                      (seq (P4String.format_t name)
                         (seq (Type.format_type_params type_params)
                            (seq space 
                               (seq ("{\n" |> text)
                                  (format_list_nl MethodPrototype.format_t methods)))))))))
        ("\n" |> text)      
    | Header { annotations; name; fields } ->
      seq (Annotation.format_ts annotations)
        (seq ("header" |> text)
           (seq space 
              (seq (P4String.format_t name)
                 (seq space
                    (format_fields fields)))))
    | HeaderUnion { annotations; name; fields } ->
      seq (Annotation.format_ts annotations)
        (box (seq ("header_union" |> text)
                (seq space 
                   (seq (P4String.format_t name)
                      (seq space
                         (format_fields fields))))))
    | NewType { annotations; name; typ_or_decl } ->
      box (seq (Annotation.format_ts annotations)
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
