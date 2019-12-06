open Util
open Sexplib.Conv
type direction =
  | In
  | Out
  | InOut
  | Directionless
  [@@deriving sexp,yojson]

type 'a info = 'a Types.info [@@deriving sexp,yojson]

module Annotation = Types.Annotation

module Op = Types.Op

module Argument = Types.Argument

module rec TypeParameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and ConstructParam : sig
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp, yojson]
end = struct
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp, yojson]
end

and Parameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and MethodPrototype : sig
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list}
        [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list}
    [@@deriving sexp,yojson]
    
  type t = pre_t info [@@deriving sexp,yojson]
end

and Expression : sig
  type pre_t =
    True
  | False
  | Int of Types.P4Int.t
  | String of Types.P4String.t
  | Name of Types.P4String.t
  | TopLevel of Types.P4String.t
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
        name: Types.P4String.t }
  | ErrorMember of Types.P4String.t
  | ExpressionMember of
      { expr: t;
        name: Types.P4String.t }
  | Ternary of
      { cond: t;
        tru: t;
        fls: t }
  | FunctionCall of
      { func: t;
        type_args: Type.t list;
        args: Expression.t list }
  | NamelessInstantiation of
      { typ: Type.t [@key "type"];
        args: Expression.t list }
  | Mask of
      { expr: t;
        mask: t }
  | Range of
      { lo: t;
        hi: t }
  [@@deriving sexp,yojson]

  and t = (pre_t * Type.t) info [@@deriving sexp,yojson]
end = struct
      type pre_t =
        True
      | False
      | Int of Types.P4Int.t
      | String of Types.P4String.t
      | Name of Types.P4String.t
      | TopLevel of Types.P4String.t
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
            name: Types.P4String.t }
      | ErrorMember of Types.P4String.t
      | ExpressionMember of
          { expr: t;
            name: Types.P4String.t }
      | Ternary of
          { cond: t;
            tru: t;
            fls: t }
      | FunctionCall of
          { func: t;
            type_args: Type.t list;
            args: Expression.t list }
      | NamelessInstantiation of
          { typ: Type.t [@key "type"];
            args: Expression.t list }
      | Mask of
          { expr: t;
            mask: t }
      | Range of
          { lo: t;
            hi: t }
            [@@deriving sexp,yojson]

      and t = (pre_t * Type.t) info [@@deriving sexp,yojson]
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

and Table : sig
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          args: Expression.t list }
      [@@deriving sexp,yojson]

      type action_ref = pre_action_ref info [@@deriving sexp,yojson]

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: Types.P4String.t }
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
              name: Types.P4String.t;
              value: Expression.t }
      [@@deriving sexp,yojson]

      type property = pre_property info [@@deriving sexp,yojson]

      val name_of_property : property -> string
    end = struct
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          args: Expression.t list }
      [@@deriving sexp,yojson]

      type action_ref = pre_action_ref info [@@deriving sexp,yojson]

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: Types.P4String.t }
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
              name: Types.P4String.t;
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

and Statement : sig
      type pre_switch_label =
          Default
        | Name of Types.P4String.t
      [@@deriving sexp,yojson]

      type switch_label = pre_switch_label info [@@deriving sexp,yojson]

      type pre_switch_case =
          Action of
            { label: switch_label;
              code: Block.t }
        | FallThrough of
            { label: switch_label }
      [@@deriving sexp,yojson]

      type switch_case = pre_switch_case info [@@deriving sexp,yojson]

      type pre_t =
          MethodCall of
            { func: Expression.t;
              type_args: Type.t list;
              args: Expression.t list }
        | Assignment of
            { lhs: Expression.t;
              rhs: Expression.t }
        | DirectApplication of
            { typ: Type.t [@key "type"];
              args: Expression.t list }
        | Conditional of
            { cond: Expression.t;
              tru: t;
              fls: t option }
        | BlockStatement of
            { block: Block.t }
        | Exit
        | EmptyStatement
        | Return of
            { expr: Expression.t option }
        | Switch of
            { expr: Expression.t;
              cases: switch_case list }
        | DeclarationStatement of
            { decl: Declaration.t }
      [@@deriving sexp,yojson]

and t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_switch_label =
      Default [@name "default"]
    | Name of Types.P4String.t [@name "name"]
  [@@deriving sexp,yojson]

  type switch_label = pre_switch_label info [@@deriving sexp,yojson]

  type pre_switch_case =
      Action of
        { label: switch_label;
          code: Block.t }
    | FallThrough of
        { label: switch_label }
  [@@deriving sexp,yojson]

  type switch_case = pre_switch_case info [@@deriving sexp,yojson]

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: Expression.t list } [@name "method_call"]
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t } [@name "assignment"]
    | DirectApplication of
        { typ: Type.t [@key "type"];
          args: Expression.t list } [@name "direct_application"]
    | Conditional of
        { cond: Expression.t;
          tru: t;
          fls: t option } [@name "conditional"]
    | BlockStatement of
        { block: Block.t } [@name "block"]
    | Exit [@name "exit"]
    | EmptyStatement [@name "empty_statement"]
    | Return of
        { expr: Expression.t option } [@name "return"]
    | Switch of
        { expr: Expression.t;
          cases: switch_case list } [@name "switch"]
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

and Parser : sig
      type pre_case =
        { matches: Match.t list;
          next: Types.P4String.t }
      [@@deriving sexp,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,yojson]

      type pre_transition =
          Direct of
            { next: Types.P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,yojson]

      type transition = pre_transition info [@@deriving sexp,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,yojson]

      type state = pre_state info [@@deriving sexp,yojson]
end = struct
      type pre_case =
        { matches: Match.t list;
          next: Types.P4String.t }
      [@@deriving sexp,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,yojson]

      type pre_transition =
          Direct of
            { next: Types.P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,yojson]

      type transition = pre_transition info [@@deriving sexp,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,yojson]

      type state = pre_state info [@@deriving sexp,yojson]
end
    
   

and Declaration : sig
  type pre_t =
    Constant of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        value: Expression.t }
  | Instantiation of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        args: Expression.t list;
        name: Types.P4String.t;
        init: Block.t option; }
  | Parser of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        constructor_params: Parameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        constructor_params: Parameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | Variable of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        init: Expression.t option }
  | ValueSet of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        size: Expression.t;
        name: Types.P4String.t }
  | Action of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Parameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        properties: Table.property list }
  | Header of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | HeaderUnion of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | Struct of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | Error of
      { members: Types.P4String.t list }
  | MatchKind of
      { members: Types.P4String.t list }
  | Enum of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        members: Types.P4String.t list }
  | SerializableEnum of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        members: (Types.P4String.t * Expression.t) list }
  | ExternObject of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        methods: MethodPrototype.t list }
  | TypeDef of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        typ_or_decl: (Type.t, t) alternative }
  | NewType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        typ_or_decl: (Type.t, t) alternative }
  | ControlType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
        [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: Types.P4String.t } [@@deriving sexp,yojson]

  and field = pre_field info [@@deriving sexp,yojson]

  val name : t -> Types.P4String.t

  val name_opt : t -> Types.P4String.t option

end = struct
  type pre_t =
    Constant of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        value: Expression.t }
  | Instantiation of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        args: Expression.t list;
        name: Types.P4String.t;
        init: Block.t option; }
  | Parser of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        constructor_params: Parameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        constructor_params: Parameter.t list;
        locals: t list;
        apply: Block.t }
        [@name "control"]
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | Variable of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        init: Expression.t option }
  | ValueSet of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        size: Expression.t;
        name: Types.P4String.t }
  | Action of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Parameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        properties: Table.property list }
  | Header of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | HeaderUnion of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | Struct of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        fields: field list }
  | Error of
      { members: Types.P4String.t list }
  | MatchKind of
      { members: Types.P4String.t list }
  | Enum of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        members: Types.P4String.t list }
  | SerializableEnum of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        members: (Types.P4String.t * Expression.t) list }
  | ExternObject of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        methods: MethodPrototype.t list }
  | TypeDef of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        typ_or_decl: (Type.t, t) alternative }
  | NewType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        typ_or_decl: (Type.t, t) alternative }
  | ControlType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Parameter.t list }
        [@@deriving sexp,yojson]

  and t = pre_t info [@@deriving sexp,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: Types.P4String.t } [@@deriving sexp,yojson]

  and field = pre_field info [@@deriving sexp,yojson]

  let name_opt d =
    match snd d with
    | Constant {name; _}
    | Instantiation {name; _}
    | Parser {name; _}
    | Control {name; _}
    | Function {name; _}
    | ExternFunction {name; _}
    | Variable {name; _}
    | ValueSet {name; _}
    | Action {name; _}
    | Table {name; _}
    | Header {name; _}
    | HeaderUnion {name; _}
    | Struct {name; _}
    | Enum {name; _}
    | SerializableEnum {name; _}
    | ExternObject {name; _}
    | TypeDef {name; _}
    | NewType {name; _}
    | ControlType {name; _}
    | ParserType {name; _}
    | PackageType {name; _} ->
       Some name
    | Error _
    | MatchKind _ ->
       None

  let name d =
    match name_opt d with
    | Some name -> name
    | None -> failwith "this declaration does not have a name"
end

and PackageType : sig
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
             [@@deriving sexp,yojson]
end = struct
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
             [@@deriving sexp,yojson]
end

and ControlType : sig
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp,yojson]
end = struct
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp,yojson]
end

and ExternType : sig
  type extern_method =
    { name: string;
      typ: FunctionType.t; }
    [@@deriving sexp,yojson]

  type t =
    { type_params: string list;
      methods: extern_method list }
    [@@deriving sexp,yojson]
end = struct
  type extern_method =
    { name: string;
      typ: FunctionType.t; }
    [@@deriving sexp,yojson]

  type t =
    { type_params: string list;
      methods: extern_method list }
    [@@deriving sexp,yojson]
end

and IntType : sig
  type t =
    { width: int }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { width: int }
    [@@deriving sexp,yojson]
end

and ArrayType : sig
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp,yojson]
end

and TupleType : sig
  type t =
    { types: Type.t list }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { types: Type.t list }
    [@@deriving sexp,yojson]
end

and RecordType : sig
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp,yojson]

  type t =
    { fields: field list; }
    [@@deriving sexp,yojson]
end = struct
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp,yojson]

  type t =
    { fields: field list; }
    [@@deriving sexp,yojson]
end

and EnumType : sig
  type t =
    { typ: Type.t option;
      members: string list; }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { typ: Type.t option;
      members: string list; }
    [@@deriving sexp,yojson]
end

and FunctionType : sig
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp,yojson]
end = struct
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp,yojson]
end

and SpecializedType : sig
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp,yojson]
end

and ActionType : sig
  type t =
    { data_params: Parameter.t list;
      ctrl_params: ConstructParam.t list}
      [@@deriving sexp,yojson]
end = struct
  type t =
  { data_params: Parameter.t list;
    ctrl_params: ConstructParam.t list}
      [@@deriving sexp,yojson]
end

and TableType : sig
  type t = {result_typ_name:string}
  [@@deriving sexp,yojson]
end = struct
  type t = {result_typ_name:string}
  [@@deriving sexp,yojson]
end

and Type : sig
  type t =
    (* bool *)
    | Bool

    (* string *)
    | String

    (* int *)
    | Integer

    (* int<width> *)
    | Int of IntType.t

    (* bit<width> *)
    | Bit of IntType.t

    (* varbit<width> *)
    | VarBit of IntType.t

    (* t[size] *)
    | Array of ArrayType.t

    (* (t1, ..., tn) *)
    | Tuple of TupleType.t

    (* A list expression (can be used as a Tuple or struct/header) *)
    | List of TupleType.t

    (* set<t> *)
    | Set of t

    (* General error type *)
    | Error

    (* match_kind *)
    | MatchKind

    (* References to other types *)
    | TypeName of string

    (* References to other types in the top-level namespace *)
    | TopLevelType of string

    (* P4 void (acts like unit) *)
    | Void

    (* header { l1: t1, ..., ln : tn } *)
    | Header of RecordType.t

    (* header union {11 : h1, ..., ln : hn} *)
    | HeaderUnion of RecordType.t

    (* struct { l1: t1, ..., ln : tn } *)
    | Struct of RecordType.t

    (* enum { l1, ..., ln } *)
    | Enum of EnumType.t

    (* Type application *)
    | SpecializedType of SpecializedType.t

    | Package of PackageType.t

    | Control of ControlType.t

    | Parser of ControlType.t

    | Extern of ExternType.t

    (* <return type> <function name>(x1,...,xn) {...} *)
    | Function of FunctionType.t

    | Action of ActionType.t

    | Table of TableType.t
    [@@deriving sexp,yojson]
end = struct
  type t =
  (* bool *)
  | Bool

  (* string *)
  | String

  (* int *)
  | Integer

  (* int<width> *)
  | Int of IntType.t

  (* bit<width> *)
  | Bit of IntType.t

  (* varbit<width> *)
  | VarBit of IntType.t

  (* t[size] *)
  | Array of ArrayType.t

  (* (t1, ..., tn) *)
  | Tuple of TupleType.t

  (* A list expression (can be used as a Tuple or struct/header) *)
  | List of TupleType.t

  (* set<t> *)
  | Set of t

  (* General error type *)
  | Error

  (* match_kind *)
  | MatchKind

  (* References to other types *)
  | TypeName of string

  (* References to other types in the top-level namespace *)
  | TopLevelType of string

  (* P4 void (acts like unit) *)
  | Void

  (* header { l1: t1, ..., ln : tn } *)
  | Header of RecordType.t

  (* header union {11 : h1, ..., ln : hn} *)
  | HeaderUnion of RecordType.t

  (* struct { l1: t1, ..., ln : tn } *)
  | Struct of RecordType.t

  (* enum { l1, ..., ln } *)
  | Enum of EnumType.t

  (* Type application *)
  | SpecializedType of SpecializedType.t

  | Package of PackageType.t

  | Control of ControlType.t

  | Parser of ControlType.t

  | Extern of ExternType.t

  (* <return type> <function name>(x1,...,xn) {...} *)
  | Function of FunctionType.t

  | Action of ActionType.t

  | Table of TableType.t
  [@@deriving sexp,yojson]
end

and StmType : sig
  type t =
  | Unit
  | Void
  [@@deriving sexp,yojson]
end = struct
  type t =
  | Unit
  | Void
  [@@deriving sexp,yojson]
end
