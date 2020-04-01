open Util

open Sexplib.Conv

type 'a info = Info.t * 'a [@@deriving sexp,yojson]

let info (i,_) = i

(* let info_to_yojson f (_,x) = f x
 *
 * let info_of_yojson f json =
 *   match f json with
 *   | Ok pre -> Ok (Info.M "<yojson>", pre)
 *   | Error x -> Error x *)

type bigint = Bigint.t [@@deriving sexp]

let bigint_to_yojson (b:bigint) : Yojson.Safe.t =
  `String (Bigint.to_string b)

let bigint_of_yojson (json:Yojson.Safe.t) =
  Ok (Bigint.of_string (Yojson.Safe.to_string json))

module P4Int = struct

  type pre_t =
    { value: bigint;
      width_signed: (int * bool) option }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

module P4String = struct
  type t = string info
  [@@deriving sexp,yojson]
end

module rec Annotation : sig
  type pre_t =
    { name: P4String.t;
      args: Argument.t list }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { name: P4String.t;
      args: Argument.t list }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and Parameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      typ: Type.t;
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      typ: Type.t [@name "type"];
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and Op : sig
  type pre_uni =
      Not
    | BitNot
    | UMinus
  [@@deriving sexp,yojson]

  type uni = pre_uni info [@@deriving sexp,yojson]

  type pre_bin =
      Plus
    | PlusSat
    | Minus
    | MinusSat
    | Mul
    | Div
    | Mod
    | Shl
    | Shr
    | Le
    | Ge
    | Lt
    | Gt
    | Eq
    | NotEq
    | BitAnd
    | BitXor
    | BitOr
    | PlusPlus
    | And
    | Or
  [@@deriving sexp,yojson]

  type bin = pre_bin info [@@deriving sexp,yojson]
end = struct
  type pre_uni =
      Not
    | BitNot
    | UMinus
  [@@deriving sexp,yojson]

  type uni = pre_uni info [@@deriving sexp,yojson]

  type pre_bin =
      Plus
    | PlusSat
    | Minus
    | MinusSat
    | Mul
    | Div
    | Mod
    | Shl
    | Shr
    | Le
    | Ge
    | Lt
    | Gt
    | Eq
    | NotEq
    | BitAnd
    | BitXor
    | BitOr
    | PlusPlus
    | And
    | Or
  [@@deriving sexp,yojson]

  type bin = pre_bin info [@@deriving sexp,yojson]
end

and Type : sig
  type pre_t =
      Bool
    | Error
    | Integer
    | IntType of Expression.t
    | BitType of Expression.t
    | VarBit of Expression.t
    | TopLevelType of P4String.t
    (* this could be a typename or a type variable. *)
    | TypeName of P4String.t
    | SpecializedType of
        { base: t;
          args: t list }
    | String
    | Void
    | DontCare
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
      Bool [@name "bool"]
    | Error [@name "error"]
    | Integer [@name "integer"]
    | IntType of Expression.t [@name "int"]
    | BitType of Expression.t  [@name "bit"]
    | VarBit of Expression.t  [@name "varbit"]
    | TopLevelType of P4String.t [@name "top_level"]
    | TypeName of P4String.t [@name "name"]
    | SpecializedType of
        { base: t;
          args: t list } [@name "specialized"]
    | String [@name "string"]
    | Void [@name "void"]
    | DontCare [@name "dont_care"]
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end

and MethodPrototype : sig
  type pre_t =
      Constructor of
        { annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list }
    | AbstractMethod of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
    | Method of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
      Constructor of
        { annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list }
    | AbstractMethod of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
    | Method of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and Argument : sig
  type pre_t  =
      Expression of
        { value: Expression.t }
    | KeyValue of
        { key: P4String.t;
          value: Expression.t }
    | Missing
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t  =
      Expression of
        { value: Expression.t }
    | KeyValue of
        { key: P4String.t;
          value: Expression.t }
    | Missing
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end
and Expression : sig
  type pre_t =
      True
    | False
    | Int of P4Int.t
    | String of P4String.t
    | Name of P4String.t
    | TopLevel of P4String.t
    | ArrayAccess of
        { array: t;
          index: t }
    | BitStringAccess of
        { bits: t;
          lo: t;
          hi: t }
    | List of
        { values: t list }
    | UnaryOp of
        { op: Op.uni;
          arg: t }
    | BinaryOp of
        { op: Op.bin;
          args: (t * t) }
    | Cast of
        { typ: Type.t;
          expr: t }
    | TypeMember of
        { typ: Type.t;
          name: P4String.t }
    | ErrorMember of P4String.t
    | ExpressionMember of
        { expr: t;
          name: P4String.t }
    | FunctionCall of
        { func: t;
          type_args: Type.t list;
          args: Argument.t list }
    | NamelessInstantiation of
        { typ: Type.t [@key "type"];
          args: Argument.t list }
    | Mask of
        { expr: t;
          mask: t }
    | Range of
        { lo: t;
          hi: t }
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
      True [@name "true"]
    | False  [@name "false"]
    | Int of P4Int.t  [@name "int"]
    | String of P4String.t [@name "string"]
    | Name of P4String.t [@name "name"]
    | TopLevel of P4String.t [@name "top_level"]
    | ArrayAccess of
        { array: t;
          index: t } [@name "array_access"]
    | BitStringAccess of
        { bits: t;
          lo: t;
          hi: t } [@name "bit_string_access"]
    | List of
        { values: t list } [@name "list"]
    | UnaryOp of
        { op: Op.uni;
          arg: t } [@name "unary_op"]
    | BinaryOp of
        { op: Op.bin;
          args: (t * t) } [@name "binary_op"]
    | Cast of
        { typ: Type.t [@key "type"];
          expr: t }  [@name "cast"]
    | TypeMember of
        { typ: Type.t [@key "type"];
          name: P4String.t } [@name "type_member"]
    | ErrorMember of P4String.t [@name "error_member"]
    | ExpressionMember of
        { expr: t;
          name: P4String.t } [@name "expression_member"]
    | FunctionCall of
        { func: t;
          type_args: Type.t list;
          args: Argument.t list } [@name "call"]
    | NamelessInstantiation of
        { typ: Type.t [@key "type"];
          args: Argument.t list } [@name "instantiation"]
    | Mask of
        { expr: t;
          mask: t } [@name "mask"]
    | Range of
        { lo: t;
          hi: t } [@name "range"]
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end

and Table : sig
  type pre_action_ref =
    { annotations: Annotation.t list;
      name: P4String.t;
      args: Argument.t list }
  [@@deriving sexp,yojson]

  type action_ref = pre_action_ref info [@@deriving sexp,yojson]

  type pre_key =
    { annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4String.t }
  [@@deriving sexp,yojson]

  type key = pre_key info [@@deriving sexp,yojson]

  type pre_entry =
    { annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,yojson { exn = true }]

  type entry = pre_entry info [@@deriving sexp,yojson]

  type pre_property =
      Key of
        { keys: key list }
    | Actions of
        { actions: action_ref list }
    | Entries of
        { entries: entry list }
    | Custom of
        { annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
  [@@deriving sexp,yojson]

  type property = pre_property info [@@deriving sexp,yojson]

  val name_of_property : property -> string
end = struct
  type pre_action_ref =
    { annotations: Annotation.t list;
      name: P4String.t;
      args: Argument.t list }
  [@@deriving sexp,yojson]

  type action_ref = pre_action_ref info [@@deriving sexp,yojson]

  type pre_key =
    { annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4String.t }
  [@@deriving sexp,yojson]

  type key = pre_key info [@@deriving sexp,yojson]

  type pre_entry =
    { annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,yojson { exn = true }]

  type entry = pre_entry info [@@deriving sexp,yojson]

  type pre_property =
      Key of
        { keys: key list }
    | Actions of
        { actions: action_ref list }
    | Entries of
        { entries: entry list }
    | Custom of
        { annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
  [@@deriving sexp,yojson]

  type property = pre_property info [@@deriving sexp,yojson]

  let name_of_property p =
    match snd p with
    | Key _ -> "key"
    | Actions _ -> "actions"
    | Entries _ -> "entries"
    | Custom {name; _} -> snd name
end

and Match : sig
  type pre_t =
      Default
    | DontCare
    | Expression of
        { expr: Expression.t }
  [@@deriving sexp,yojson { exn = true }]

  type t = pre_t info [@@deriving sexp,yojson { exn = true }]
end = struct
  type pre_t =
      Default
    | DontCare
    | Expression of
        { expr: Expression.t }
  [@@deriving sexp,yojson { exn = true }]

  type t = pre_t info [@@deriving sexp,yojson { exn = true }]
end

and Declaration : sig
  type pre_t =
      Constant of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
    | Instantiation of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
    | Function of
        { return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | Action of
        { annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
    | Variable of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
    | Struct of
        { annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Error of
        { members: P4String.t list }
    | ExternObject of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,yojson]

  and field = pre_field info [@@deriving sexp,yojson]

  val name : t -> P4String.t

  val name_opt : t -> P4String.t option

end = struct
  type pre_t =
      Constant of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
    | Instantiation of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
    | Function of
        { return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | Action of
        { annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
    | Variable of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
    | Struct of
        { annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Error of
        { members: P4String.t list }
    | ExternObject of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,yojson]

  and field = pre_field info [@@deriving sexp,yojson]

  let name_opt d =
    match snd d with
    | Constant {name; _}
    | Instantiation {name; _}
    | Function {name; _}
    | ExternFunction {name; _}
    | Action {name; _}
    | Table {name; _}
    | Variable {name; _}
    | Struct {name; _}
    | ExternObject {name; _}
    | TypeDef {name; _}
    | NewType {name; _} ->
      Some name
    | Error _ ->
      None

  let name d =
    match name_opt d with
    | Some name -> name
    | None -> failwith "this declaration does not have a name"
end

and Statement : sig

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list }
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t }
    | DirectApplication of
        { typ: Type.t [@key "type"];
          args: Argument.t list }
    | Conditional of
        { cond: Expression.t;
          tru: t;
          fls: t option }
    | While of
        { cond: Expression.t;
          body: t }
    | BlockStatement of
        { block: Block.t }
    | Exit
    | EmptyStatement
    | Return of
        { expr: Expression.t option }
    | DeclarationStatement of
        { decl: Declaration.t }
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end = struct

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list } [@name "method_call"]
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t } [@name "assignment"]
    | DirectApplication of
        { typ: Type.t [@key "type"];
          args: Argument.t list } [@name "direct_application"]
    | Conditional of
        { cond: Expression.t;
          tru: t;
          fls: t option } [@name "conditional"]
    | While of
        { cond: Expression.t;
          body: t } [@name "while"]
    | BlockStatement of
        { block: Block.t } [@name "block"]
    | Exit [@name "exit"]
    | EmptyStatement [@name "empty_statement"]
    | Return of
        { expr: Expression.t option } [@name "return"]
    | DeclarationStatement of
        { decl: Declaration.t } [@name "declaration"]
  [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]
end
and Block : sig
  type pre_t =
    { annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

type program =
    Program of (Declaration.t list * Expression.t) [@name "program"]
[@@deriving sexp,yojson]
