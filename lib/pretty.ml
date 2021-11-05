(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *)

open Core_kernel
open Util
module P4 = Types

let format_list f fmt l =
  List.iter l ~f:(f fmt)

let format_list_nl f fmt l =
  let g b x =
    if b then Format.fprintf fmt "@\n";
    f fmt x;
    true in
  ignore (List.fold_left l ~init:false ~f:g)

let format_list_sep f sep fmt l =
  let g b x =
    if b then Format.fprintf fmt "%s" sep;
    Format.fprintf fmt "@,";
    f fmt x;
    true in
  ignore (List.fold_left l ~init:false ~f:g)

let format_list_term f term fmt l =
  let g x =
    f fmt x;
    Format.fprintf fmt "%s@," term in
  List.iter l ~f:g

let format_list_sep_nl f sep fmt l =
  let g b x =
    if b then Format.fprintf fmt "%s@\n" sep;
    f fmt x;
    true in
  ignore (List.fold_left l ~init:false ~f:g)

let format_option f fmt o =
  match o with
  | None ->
    ()
  | Some x ->
    f fmt x

module P4Int = struct
  let format_bigint fmt b =
    Format.fprintf fmt "%s" (Bigint.to_string b)

  let format_t fmt (i: P4int.t) =
    Format.fprintf fmt "@[";
    (match i.width_signed with
     | None ->
       ()
     | Some (width,signed) ->
       Format.fprintf fmt "%d%s" width (if signed then "s" else "w"));
    format_bigint fmt i.value;
    Format.fprintf fmt "@]";
end

module P4String = struct
  let format_t fmt (e: P4string.t) =
    Format.fprintf fmt "%s" e.str
end

let name_format_t fmt (name: P4name.t) =
  match name with
  | BareName str ->
     P4String.format_t fmt str
  | QualifiedName ([], str) ->
     Format.fprintf fmt ".%a"
       P4String.format_t str 
  | _ -> failwith "unimplemented"

module rec Expression : sig
  val format_t : Format.formatter -> P4.Expression.t -> unit
end = struct
  open P4.Expression
  let rec format_t fmt e =
    match snd e with
    | True ->
      Format.fprintf fmt "true"
    | False ->
      Format.fprintf fmt "false"
    | Int i ->
      Format.fprintf fmt "%a"
        P4Int.format_t i
    | String s ->
      Format.fprintf fmt "\"%a\""
        P4String.format_t s
    | Name name ->
      Format.fprintf fmt "%a"
        name_format_t name
    | ArrayAccess x ->
      Format.fprintf fmt "@[%a[%a]@]"
        format_t x.array
        format_t x.index
    | BitStringAccess x ->
      Format.fprintf fmt "@[%a[%a:%a]@]"
        format_t x.bits
        format_t x.hi
        format_t x.lo
    | List x ->
      Format.fprintf fmt "@[<4>{%a}@]" 
        (format_list_sep format_t ",") x.values
    | Record x ->
      Format.fprintf fmt "@[<4>{%a}@]"
        (format_list_sep KeyValue.format_t ",") x.entries
    | UnaryOp x ->
      let uop = match (snd x.op) with
      | Not -> "!"
      | BitNot -> "~"
      | UMinus -> "-"
      in
      Format.fprintf fmt "@[<4>(%s@ %a)@]"
        uop
        format_t x.arg
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
      in
      Format.fprintf fmt "@[<4>(%a@ %s@ %a)@]"
        format_t (fst x.args)
        bop
        format_t (snd x.args)
    | Cast x ->
      Format.fprintf fmt "@[<4>(%a)(%a)@]"
        Type.format_t x.typ
        format_t x.expr
    | TypeMember x ->
      Format.fprintf fmt "@[<4>%a.%s@]"
        name_format_t x.typ
        x.name.str
    | ErrorMember x ->
      Format.fprintf fmt "@[<4>error.%s@]" x.str
    | ExpressionMember x ->
      Format.fprintf fmt "@[<4>%a.%s@]"
        format_t x.expr
        x.name.str
    | Ternary x ->
      Format.fprintf fmt "@[<4>(%a ?@ %a@ :@ %a)@]"
        format_t x.cond
        format_t x.tru
        format_t x.fls
    | FunctionCall x ->
      Format.fprintf fmt "@[<4>%a%a(%a)@]"
        format_t x.func
        Type.format_typ_args x.type_args
        (format_list_sep Argument.format_t ",") x.args
    | NamelessInstantiation x ->
      Format.fprintf fmt "@[<4>%a(%a)@]"
        Type.format_t x.typ
        (format_list_sep Argument.format_t ",") x.args
    | Mask x ->
      Format.fprintf fmt "@[<4>%a@ &&&@ %a@]"
      format_t x.expr
      format_t x.mask
    | Range x ->
      Format.fprintf fmt "@[<4>%a@ ..@ %a@]" (* TODO: check *)
        format_t x.lo
        format_t x.hi

end

and Statement : sig
  val format_t : Format.formatter -> P4.Statement.t -> unit
end = struct
  open P4.Statement

  let format_switch_label fmt sl =
    match sl with
    | Default ->
      Format.fprintf fmt "default"
    | Name(sl) ->
       Format.fprintf fmt "@[%a@]"
        P4String.format_t sl

  let format_switch_case fmt sc =
    match snd sc with
    | Action { label; code } ->
       Format.fprintf fmt "%a: %a"
         format_switch_label (snd label)
         Block.format_t code
    | FallThrough { label } ->
       Format.fprintf fmt "%a:"
        format_switch_label (snd label)     

  let rec format_t fmt (e:t) =
    match snd e with
    | MethodCall { func; type_args; args } ->
      Format.fprintf fmt "@[%a%a(%a);@]"
        Expression.format_t func
        Type.format_typ_args type_args
        Argument.format_ts args
    | Assignment { lhs; rhs } ->
      Format.fprintf fmt "@[%a = %a;@]"
        Expression.format_t lhs
        Expression.format_t rhs
    | DirectApplication { typ; args } ->
      Format.fprintf fmt "@[%a.apply(%a);@]"
        Type.format_t typ
        Argument.format_ts args
    | Conditional { cond; tru; fls } ->
        Format.fprintf fmt "@[<4>if (%a)@ "
          Expression.format_t cond;
        (match snd tru with
         | BlockStatement { block=tru_block } ->
           Block.format_t fmt tru_block;
           (match fls with
            | None ->
              ()
            | Some (_, BlockStatement { block=fls_block }) ->
              Format.fprintf fmt "@[<4>else@ %a"
                Block.format_t fls_block
            | Some sfls ->
              Format.fprintf fmt "@\nelse@ %a"
                format_t sfls)
         | _ ->
           Format.fprintf fmt "@\n%a@]" format_t tru;
           (match fls with
            | None ->
              ()
            | Some (_, BlockStatement { block=fls_block }) ->
              Format.fprintf fmt "@\n@[<4>else@ %a"
                Block.format_t fls_block
            | Some sfls ->
              Format.fprintf fmt "@\n@[<4>else@\n%a@]"
                format_t sfls));
    | BlockStatement { block } ->
      Format.fprintf fmt "@[<4>%a"
        Block.format_t block
    | Exit ->
      Format.fprintf fmt "exit;"
    | EmptyStatement ->
      Format.fprintf fmt ";"
    | Return { expr = None } ->
      Format.fprintf fmt "return;"
    | Return { expr = Some sexpr } ->
      Format.fprintf fmt "@[return %a;@]"
        Expression.format_t sexpr
    | Switch { expr; cases } -> 
       Format.fprintf fmt "@[<4>switch (%a) {%a@]@\n}"
         Expression.format_t expr
         (format_list_nl format_switch_case) cases
    | DeclarationStatement { decl } ->
      Declaration.format_t fmt decl
end

and Block : sig
  val format_t : Format.formatter -> P4.Block.t -> unit
end = struct
  open P4.Block
  let format_t fmt e =
    match snd e with
    | { annotations=[]; statements=[] } ->
      Format.fprintf fmt "{ }@]"
    | { annotations; statements } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "{@\n%a@]@\n}"
        (format_list_nl Statement.format_t) statements;
end

and Argument : sig
  val format_t : Format.formatter -> P4.Argument.t -> unit
  val format_ts : Format.formatter -> P4.Argument.t list -> unit
end = struct
  open P4.Argument
  let format_t fmt e =
    match snd e with
    | Expression x ->
      Format.fprintf fmt "@[%a@]"
        Expression.format_t x.value
    | KeyValue x ->
      Format.fprintf fmt "@[<4>%s=%a@]"
        x.key.str
        Expression.format_t x.value
    | Missing ->
      Format.fprintf fmt "_"
  let format_ts fmt l =
    Format.fprintf fmt "@[%a@]"
      (format_list_sep format_t ",") l
end

and Type : sig
  val format_t : Format.formatter -> P4.Type.t -> unit
  val format_typ_args: Format.formatter -> P4.Type.t list -> unit
  val format_type_params: Format.formatter -> P4string.t list -> unit
end = struct
  open P4.Type
  let rec format_t fmt e =
    match snd e with
    | Bool ->
      Format.fprintf fmt "bool"
    | Error ->
      Format.fprintf fmt "error"
    | Integer ->
      Format.fprintf fmt "int"
    | IntType x ->
      Format.fprintf fmt "@[int<%a>@]"
        Expression.format_t x
    | BitType e -> 
       begin match snd e with 
       | P4.Expression.Int _  -> 
          Format.fprintf fmt "@[bit<%a>@]"
            Expression.format_t e
       | _ -> 
          Format.fprintf fmt "@[bit<(%a)>@]"
            Expression.format_t e
       end
    | VarBit x ->
      Format.fprintf fmt "@[varbit@ <%a>@]"
        Expression.format_t x
    | TypeName (BareName x) ->
      Format.fprintf fmt "@[%s@]"
        x.str
    | TypeName (QualifiedName ([], x)) ->
      Format.fprintf fmt "@[.%s@]"
        x.str;
    | TypeName _ ->
       failwith "unimplemented"
    | SpecializedType x ->
      Format.fprintf fmt "@[%a<%a>@]"
        format_t x.base
        (format_list_sep format_t ",") x.args
    | HeaderStack x ->
      Format.fprintf fmt "@[%a[%a]@]"
        format_t x.header
        Expression.format_t x.size
    | Tuple x ->
      Format.fprintf fmt "@[tuple<%a>@]"
        (format_list_sep format_t ",") x
    | String -> 
       Format.fprintf fmt "string"      
    | Void ->
      Format.fprintf fmt "void"
    | DontCare ->
      Format.fprintf fmt "_"

  let format_typ_args fmt l =
    if List.is_empty l then
      ()
    else
      Format.fprintf fmt "<%a>"
        (format_list_sep format_t ",") l

  let format_type_params fmt l =
    if List.is_empty l then
      ()
    else
      Format.fprintf fmt "<%a>"
        (format_list_sep P4String.format_t ",") l
end

and KeyValue : sig 
  val format_t : Format.formatter -> P4.KeyValue.t -> unit
end = struct
  open P4.KeyValue
  let format_t fmt kv = 
    match snd kv with 
    | { key; value } -> 
       Format.fprintf fmt "%a = %a" 
         P4String.format_t key 
         Expression.format_t value 
end

and Annotation : sig
  val format_t : Format.formatter -> P4.Annotation.t -> unit
  val format_ts : Format.formatter -> P4.Annotation.t list -> unit
end = struct
  open P4.Annotation
  let format_body fmt body = 
    match snd body with 
    | Empty -> 
       ()
    | Unparsed strings -> 
       Format.fprintf fmt "(%a)" 
         (format_list_sep P4String.format_t " ") strings
    | Expression exprs -> 
       Format.fprintf fmt "[%a]" 
         (format_list_sep Expression.format_t ",") exprs
    | KeyValue kvs -> 
       Format.fprintf fmt "{%a}" 
         (format_list_sep KeyValue.format_t ",") kvs

  let format_t fmt e =
    match snd e with 
    | { name; body } -> 
       Format.fprintf fmt "@[%@%a%a@]"
         P4String.format_t name
         format_body body
      
  let format_ts fmt l =
    match l with
    | [] ->
      ()
    | _ :: _ ->
      (format_list_nl format_t fmt l;
       Format.fprintf fmt "@\n")
end

and Direction : sig
  val format_t : Format.formatter -> P4.Direction.t -> unit
end = struct
  open P4.Direction
  let format_t fmt e =
    match snd e with
    | In -> Format.fprintf fmt "in"
    | Out -> Format.fprintf fmt "out"
    | InOut -> Format.fprintf fmt "inout"
end

and Parameter : sig
  val format_t : Format.formatter -> P4.Parameter.t -> unit
  val format_params : Format.formatter -> P4.Parameter.t list -> unit
  val format_constructor_params : Format.formatter -> P4.Parameter.t list -> unit
end = struct
  open P4.Parameter
  let format_t fmt e =
    let p = snd e in
    Annotation.format_ts fmt p.annotations;
    Format.fprintf fmt "@[%a%s%a %s%a@]"
      (format_option Direction.format_t) p.direction
      (match p.direction with None -> "" | Some _ -> " ")
      Type.format_t p.typ
      p.variable.str
      (format_option
         (fun fmt e ->
            Format.fprintf fmt "= %a" Expression.format_t e)) p.opt_value

  let format_params fmt l =
    Format.fprintf fmt "@[%a@]" (format_list_sep format_t ",") l

  let format_constructor_params fmt l =
    match l with
    | [] ->
      ()
    | _ :: _ ->
      Format.fprintf fmt "(@[%a@])"
        (format_list_sep format_t ",") l

end

and Match: sig
  val format_t : Format.formatter -> P4.Match.t -> unit
  val format_ts : Format.formatter -> P4.Match.t list -> unit
end = struct
  open P4.Match
  let format_t fmt e =
    match snd e with
    | Default ->
      Format.fprintf fmt "default"
    | DontCare ->
      Format.fprintf fmt "_"
    | Expression { expr } ->
      Expression.format_t fmt expr

  let format_ts fmt l =
    match l with
    | [] ->
      ()
    | [x] ->
      format_t fmt x
    | _ ->
      Format.fprintf fmt "@[(%a)@]"
        (format_list_sep format_t ",") l
end

and Parser : sig
  val format_state : Format.formatter -> P4.Parser.state -> unit
  val format_states : Format.formatter -> P4.Parser.state list -> unit
end = struct
  open P4.Parser

  let format_case fmt e =
    match snd e with
    | { matches; next } ->
      Format.fprintf fmt "%a: %a;"
        Match.format_ts matches
        P4String.format_t next

  let format_transition fmt e =
    match snd e with
    | Direct { next } ->
      Format.fprintf fmt "transition %a;"
        P4String.format_t next
    | Select { exprs; cases } ->
      Format.fprintf fmt "@[<4>transition select(%a) {%a@]@\n}"
        (format_list_sep Expression.format_t ",") exprs
      (format_list_nl format_case) cases

  let format_state fmt e =
    match snd e with
    | { annotations; name; statements; transition } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>state %a {@\n%a"
        P4String.format_t name
        (format_list_nl Statement.format_t) statements;
      (match statements with [] -> () | _ :: _ -> Format.fprintf fmt "@\n");
      Format.fprintf fmt "%a@]@\n}" format_transition transition

  let format_states fmt l =
    format_list_nl format_state fmt l
end

and Table : sig
  val format_property : Format.formatter -> P4.Table.property -> unit
end = struct
  open P4.Table

  let format_key fmt e = 
    match snd e with 
    | { annotations; key; match_kind } -> 
      Format.fprintf fmt "@[%a@ :@ %a %a;@]"
        Expression.format_t key
        P4String.format_t match_kind
        Annotation.format_ts annotations      

  let format_action_ref fmt e =
    match snd e with
    | { annotations; name; args = [] } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a@]"
        name_format_t name
    | { annotations; name; args } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a(%a)@]"
        name_format_t name
        Argument.format_ts args

  let format_entry fmt e =
    match snd e with
    | { annotations; matches; action } ->
      Format.fprintf fmt "@[%a : %a@]"
        Match.format_ts matches
        format_action_ref action;
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt ";"

  let format_property fmt e =
    match snd e with
    | Key { keys } ->
      Format.fprintf fmt "@[<4>key = {@\n%a@]@\n}"
        (format_list_nl format_key) keys
    | Actions { actions } ->
      Format.fprintf fmt "@[<4>actions = {@\n%a@]@\n}"
        (format_list_term format_action_ref ";") actions
    | Entries { entries } ->
      Format.fprintf fmt "@[<4>const entries = {@\n%a@]@\n}"
        (format_list_nl format_entry) entries
    | Custom { annotations; const; name; value } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%s%a = %a;@]"
        (if const then "const " else "")
        P4String.format_t name
        Expression.format_t value
end

and MethodPrototype : sig
  val format_t : Format.formatter -> P4.MethodPrototype.t -> unit
end = struct
  open P4.MethodPrototype
  let format_t fmt e =
    match snd e with
    | Constructor { annotations; name; params } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a(%a);@]"
        P4String.format_t name
        Parameter.format_params params
    | Method { annotations; return; name; type_params; params } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a %a%a(%a);@]"
        Type.format_t return
        P4String.format_t name
        Type.format_type_params type_params
        Parameter.format_params params
    | AbstractMethod { annotations; return; name; type_params; params } -> 
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[abstract %a %a%a(%a);@]"
        Type.format_t return
        P4String.format_t name
        Type.format_type_params type_params
        Parameter.format_params params
end


and Declaration : sig
  val format_t : Format.formatter -> P4.Declaration.t -> unit
end = struct
  open P4.Declaration

  let format_field fmt f =
    match snd f with
    | { annotations; typ; name } ->
      Format.fprintf fmt "@[%a@]"
        Annotation.format_ts annotations;
      Format.fprintf fmt "@[%a %a;@]"
        Type.format_t typ
        P4String.format_t name

  let format_fields fmt l =
    match l with
    | [] ->
      Format.fprintf fmt "{ }@]"
    | _ :: _ ->
      Format.fprintf fmt "{@\n%a@]@\n}"
        (format_list_nl format_field) l

  let rec format_typ_or_decl fmt td =
    match td with
    | Left(typ) ->
      Type.format_t fmt typ
    | Right(decl) ->
      format_t fmt decl

  and format_t fmt e =
    match snd e with
    | Constant { annotations; typ; name; value } ->
      Format.fprintf fmt "@[<4>%aconst %a %s = %a;@]"
        Annotation.format_ts annotations
        Type.format_t typ
        name.str
        Expression.format_t value
    | Action { annotations; name; params; body } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>action %s(@[%a@]) %a"
        name.str
        Parameter.format_params params
        Block.format_t body
    | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>control %s%a(%a)%a {@\n"
        name.str
        Type.format_type_params type_params
        Parameter.format_params params
        Parameter.format_constructor_params constructor_params;
      if not (List.is_empty locals) then 
        Format.fprintf fmt "%a@\n" (format_list_nl format_t) locals;
      Format.fprintf fmt "@[<4>apply %a" Block.format_t apply;
      Format.fprintf fmt "@]@\n}"
    | Parser { annotations; name; type_params; params; constructor_params; locals; states } ->
      Format.fprintf fmt "@[%a" Annotation.format_ts annotations;
      Format.fprintf fmt "@[<4>parser %s%a(%a)%a {@\n"
        name.str
        Type.format_type_params type_params
        Parameter.format_params params
        Parameter.format_constructor_params constructor_params;
      if not (List.is_empty locals) then 
        Format.fprintf fmt "%a@\n" (format_list_nl format_t) locals;
      Parser.format_states fmt states;
      Format.fprintf fmt "@]@\n}"
    | Instantiation { annotations; typ; args; name; init=None } -> 
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a(%a) %a;@]"
        Type.format_t typ
        Argument.format_ts args
        P4String.format_t name
    | Instantiation { annotations; typ; args; name; init=Some block } -> 
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>%a(%a) %a = %a;"
        Type.format_t typ
        Argument.format_ts args
        P4String.format_t name
        Block.format_t block
    | Table { annotations; name; properties } -> 
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>table %a {@\n%a@]@\n}"
        P4String.format_t name
        (format_list_nl Table.format_property) properties
    | Variable { annotations; typ; name; init = None } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[%a %a;@]"
        Type.format_t typ
        P4String.format_t name
    | Variable { annotations; typ; name; init = Some sinit } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>%a %a = %a;@]"
        Type.format_t typ
        P4String.format_t name
        Expression.format_t sinit;
    | ExternFunction { annotations; return; name; type_params; params } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[extern %a %a%a(%a);@]"
        Type.format_t return
        P4String.format_t name
        Type.format_type_params type_params
        Parameter.format_params params
    | Function { return; name; type_params; params; body } ->
      Format.fprintf fmt "@[<4>%a %a%a(%a) %a"
        Type.format_t return
        P4String.format_t name
        Type.format_type_params type_params
        Parameter.format_params params
        Block.format_t body
    | ValueSet { annotations; typ; size; name } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[value_set<%a>(%a) %a;@]"
        Type.format_t typ
        Expression.format_t size
        P4String.format_t name
    | TypeDef { annotations; name; typ_or_decl } ->
      Format.fprintf fmt "@[%atypedef %a %s;@]"
        Annotation.format_ts annotations
        format_typ_or_decl typ_or_decl
        name.str
    | ControlType { annotations; name; type_params; params } ->
      Format.fprintf fmt "@[<4>%acontrol %s%a@,(@[%a@]);@]"
        Annotation.format_ts annotations
        name.str
        Type.format_type_params type_params
        (format_list_sep Parameter.format_t ",") params
    | ParserType { annotations; name; type_params; params } ->
      Format.fprintf fmt "@[<4>%aparser %s%a@,(@[%a@]);@]"
        Annotation.format_ts annotations
        name.str
        Type.format_type_params type_params
        (format_list_sep Parameter.format_t ",") params
    | PackageType { annotations; name; type_params; params } ->
      Format.fprintf fmt "@[<4>%apackage %s%a@,(@[%a@]);@]"
        Annotation.format_ts annotations
        name.str
        Type.format_type_params type_params
        (format_list_sep Parameter.format_t ",") params
    | Struct { annotations; name; fields } ->
        Format.fprintf fmt "@[%a@]"
          Annotation.format_ts annotations;
        Format.fprintf fmt "@[<4>struct %a %a"
          P4String.format_t name
          format_fields fields
    | MatchKind { members=[] } ->
      Format.fprintf fmt "@[<4>match_kind { }@]";
    | MatchKind { members } ->
      Format.fprintf fmt "@[<4>match_kind {@\n%a@]@\n}"
        (format_list_sep_nl P4String.format_t ",") members
    | Error { members=[] } ->
      Format.fprintf fmt "@[<4>error { }@]";
    | Error { members } ->
      Format.fprintf fmt "@[<4>error {@\n%a@]@\n}"
        (format_list_sep_nl P4String.format_t ",") members
    | Enum { annotations; name; members=[] } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>enum %a { }@]"
        P4String.format_t name
    | Enum { annotations; name; members } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>enum %a {@\n%a@]@\n}"
        P4String.format_t name
        (format_list_sep_nl P4String.format_t ",") members
    | SerializableEnum { annotations; typ; name; members=[] } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>enum %a %a { }@]"
        Type.format_t typ
        P4String.format_t name
    | SerializableEnum { annotations; typ; name; members } ->
      let format_member fmt (field,init) =
        Format.fprintf fmt "%a = %a"
          P4String.format_t field
          Expression.format_t init in
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>enum %a %a {@\n%a@]@\n}"
        Type.format_t typ
        P4String.format_t name
        (format_list_sep_nl format_member ",") members
    | ExternObject { annotations; name; type_params; methods = [] } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[extern %a%a { }@]"
        P4String.format_t name
        Type.format_type_params type_params
    | ExternObject { annotations; name; type_params; methods } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>extern %a%a {@\n"
        P4String.format_t name
        Type.format_type_params type_params;
      format_list_nl MethodPrototype.format_t fmt methods;
      Format.fprintf fmt "@]@\n}"
    | Header { annotations; name; fields } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>header %a %a"
        P4String.format_t name
        format_fields fields
    | HeaderUnion { annotations; name; fields } ->
      Annotation.format_ts fmt annotations;
      Format.fprintf fmt "@[<4>header_union %a %a"
        P4String.format_t name
        format_fields fields
    | NewType { annotations; name; typ_or_decl } ->
      Format.fprintf fmt "@[%atype %a %s;@]"
        Annotation.format_ts annotations
        format_typ_or_decl typ_or_decl
        name.str
end

let format_program fmt p =
  match p with
  | P4.Program(ds) ->
    Format.fprintf fmt "@[%a@\n@]"
      (format_list_nl Declaration.format_t) ds
