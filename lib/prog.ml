module I = Info
open Util
open Core_kernel
module Info = I

open Typed

module P4Int = Types.P4Int

module P4String = Types.P4String

module rec MethodPrototype : sig
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Typed.Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list}
        [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: Typed.Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list}
    [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

and KeyValue : sig
  type pre_t =
    { key : P4String.t;
      value : Expression.t }
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_t =
    { key : P4String.t;
      value : Expression.t }
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

and Expression : sig
  type pre_t =
    True
  | False
  | Int of P4Int.t
  | String of Types.P4String.t
  | Name of Types.name
  | ArrayAccess of
      { array: t;
        index: t }
  | BitStringAccess of
      { bits: t;
        lo: Util.bigint;
        hi: Util.bigint }
  | List of
      { values: t list }
  | Record of
      { entries: KeyValue.t list }
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
      { typ: Types.name;
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
        args: (t option) list }
  | NamelessInstantiation of
      { typ: Type.t [@key "type"];
        args: t list }
  | DontCare
  | Mask of
      { expr: t;
        mask: t }
  | Range of
      { lo: t;
        hi: t }
  [@@deriving sexp,show,yojson]

  and typed_t = { expr: pre_t;
                  typ: Type.t;
                  dir: direction }
  and t = typed_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_t =
    True
  | False
  | Int of P4Int.t
  | String of Types.P4String.t
  | Name of Types.name
  | ArrayAccess of
      { array: t;
        index: t }
  | BitStringAccess of
      { bits: t;
        lo: bigint;
        hi: bigint }
  | List of
      { values: t list }
  | Record of
      { entries: KeyValue.t list }
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
      { typ: Types.name;
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
        args: (t option) list }
  | NamelessInstantiation of
      { typ: Type.t [@key "type"];
        args: Expression.t list }
  | DontCare
  | Mask of
      { expr: t;
        mask: t }
  | Range of
      { lo: t;
        hi: t }
        [@@deriving sexp,show,yojson]

  and typed_t = { expr: pre_t;
                  typ: Type.t;
                  dir: direction }
  and t = typed_t info [@@deriving sexp,show,yojson]
end

and Match : sig
  type pre_t =
    DontCare
  | Expression of
      { expr: Expression.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type typed_t = { expr: pre_t;
                   typ: Type.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type t = typed_t info [@@deriving sexp,show,yojson { exn = true }]
end = struct
  type pre_t =
    DontCare
  | Expression of
      { expr: Expression.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type typed_t = { expr: pre_t;
                   typ: Type.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type t = typed_t info [@@deriving sexp,show,yojson { exn = true }]
end

and Table : sig
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: Types.name;
          args: (Expression.t option) list }
      [@@deriving sexp,show,yojson]

      type typed_action_ref =
        { action: pre_action_ref;
          typ: Typed.Type.t }
      [@@deriving sexp,show,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,show,yojson]

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: Types.P4String.t }
      [@@deriving sexp,show,yojson]

      type key = pre_key info [@@deriving sexp,show,yojson]

      type pre_entry =
        { annotations: Annotation.t list;
          matches: Match.t list;
          action: action_ref }
      [@@deriving sexp,show,yojson { exn = true }]

      type entry = pre_entry info [@@deriving sexp,show,yojson]

      type pre_property =
        { annotations: Annotation.t list;
          const: bool;
          name: Types.P4String.t;
          value: Expression.t }
      [@@deriving sexp,show,yojson]

      type property = pre_property info [@@deriving sexp,show,yojson]

      val name_of_property : property -> string
    end = struct
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: Types.name;
          args: (Expression.t option) list }
      [@@deriving sexp,show,yojson]

      type typed_action_ref =
        { action: pre_action_ref;
          typ: Typed.Type.t }
      [@@deriving sexp,show,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,show,yojson]

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: Types.P4String.t }
      [@@deriving sexp,show,yojson]

      type key = pre_key info [@@deriving sexp,show,yojson]

      type pre_entry =
        { annotations: Annotation.t list;
          matches: Match.t list;
          action: action_ref }
      [@@deriving sexp,show,yojson { exn = true }]

      type entry = pre_entry info [@@deriving sexp,show,yojson]

      type pre_property =
        { annotations: Annotation.t list;
          const: bool;
          name: Types.P4String.t;
          value: Expression.t }
      [@@deriving sexp,show,yojson]

      type property = pre_property info [@@deriving sexp,show,yojson]

      let name_of_property (_, {name; _}) =
        snd name
end

and Statement : sig
      type pre_switch_label =
          Default
        | Name of Types.P4String.t
      [@@deriving sexp,show,yojson]

      type switch_label = pre_switch_label info [@@deriving sexp,show,yojson]

      type pre_switch_case =
          Action of
            { label: switch_label;
              code: Block.t }
        | FallThrough of
            { label: switch_label }
      [@@deriving sexp,show,yojson]

      type switch_case = pre_switch_case info [@@deriving sexp,show,yojson]

      type pre_t =
          MethodCall of
            { func: Expression.t;
              type_args: Type.t list;
              args: (Expression.t option) list }
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
      [@@deriving sexp,show,yojson]

      and typed_t =
        { stmt: pre_t;
          typ: StmType.t }

      and t = typed_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_switch_label =
      Default [@name "default"]
    | Name of Types.P4String.t [@name "name"]
  [@@deriving sexp,show,yojson]

  type switch_label = pre_switch_label info [@@deriving sexp,show,yojson]

  type pre_switch_case =
      Action of
        { label: switch_label;
          code: Block.t }
    | FallThrough of
        { label: switch_label }
  [@@deriving sexp,show,yojson]

  type switch_case = pre_switch_case info [@@deriving sexp,show,yojson]

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: (Expression.t option) list } [@name "method_call"]
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
  [@@deriving sexp,show,yojson]

  and typed_t =
    { stmt: pre_t;
      typ: StmType.t }

  and t = typed_t info [@@deriving sexp,show,yojson]
end

and Block : sig
  type pre_t =
    { annotations: Annotation.t list;
      statements: Statement.t list }
      [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      statements: Statement.t list }
      [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

and Parser : sig
      type pre_case =
        { matches: Match.t list;
          next: Types.P4String.t }
      [@@deriving sexp,show,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,show,yojson]

      type pre_transition =
          Direct of
            { next: Types.P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,show,yojson]

      type transition = pre_transition info [@@deriving sexp,show,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,show,yojson]

      type state = pre_state info [@@deriving sexp,show,yojson]
end = struct
      type pre_case =
        { matches: Match.t list;
          next: Types.P4String.t }
      [@@deriving sexp,show,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,show,yojson]

      type pre_transition =
          Direct of
            { next: Types.P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,show,yojson]

      type transition = pre_transition info [@@deriving sexp,show,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: Types.P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,show,yojson]

      type state = pre_state info [@@deriving sexp,show,yojson]
end

and Declaration : sig
  type pre_t =
    Constant of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        value: Value.value }
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
        params: Typed.Parameter.t list;
        constructor_params: Typed.Parameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list;
        constructor_params: Typed.Parameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
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
        data_params: Typed.Parameter.t list;
        ctrl_params: Typed.Parameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        key: Table.key list;
        actions: Table.action_ref list;
        entries: (Table.entry list) option;
        default_action: Table.action_ref option;
        size: P4Int.t option;
        custom_properties: Table.property list }
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
        params: Typed.Parameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
        [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: Types.P4String.t } [@@deriving sexp,show,yojson]

  and field = pre_field info [@@deriving sexp,show,yojson]

  val name : t -> Types.P4String.t

  val name_opt : t -> Types.P4String.t option

end = struct
  type pre_t =
    Constant of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: Types.P4String.t;
        value: Value.value }
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
        params: Typed.Parameter.t list;
        constructor_params: Typed.Parameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list;
        constructor_params: Typed.Parameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
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
        data_params: Typed.Parameter.t list;
        ctrl_params: Typed.Parameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        key: Table.key list;
        actions: Table.action_ref list;
        entries: (Table.entry list) option;
        default_action: Table.action_ref option;
        size: P4Int.t option;
        custom_properties: Table.property list }
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
        params: Typed.Parameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: Typed.Parameter.t list }
        [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]

  and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: Types.P4String.t } [@@deriving sexp,show,yojson]

  and field = pre_field info [@@deriving sexp,show,yojson]

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

and Value : sig
  type buf = Cstruct_sexp.t [@@deriving sexp,show]
  (* let buf_to_yojson b = failwith "unimplemented"
  let buf_of_yojson j = failwith "unimplemented" *)

  type pkt = {
    emitted : buf;
    main : buf;
    in_size : int;
  } [@@deriving sexp,show,yojson]

  type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list * (Ast.qualified_name * Ast.action list) list

  type vsets = Match.t list list

  type ctrl = entries * vsets

  type loc = string [@@deriving sexp, show,yojson]

  type value =
    | VNull
    | VBool of bool
    | VInteger of Bigint.t
    | VBit of
        { w : Bigint.t;
          v : Bigint.t; }
    | VInt of
        { w : Bigint.t;
          v : Bigint.t; }
    | VVarbit of
        { max : Bigint.t;
          w : Bigint.t;
          v : Bigint.t; }
    | VString of string
    | VTuple of value list
    | VRecord of (string * value) list
    | VSet of set
    | VError of string
    | VMatchKind of string
    | VFun of
        { scope : Env.EvalEnv.t;
          params : Typed.Parameter.t list;
          body : Block.t; }
    | VBuiltinFun of
        { name : string;
          caller : lvalue; }
    | VAction of
        { scope : Env.EvalEnv.t;
          params : Typed.Parameter.t list;
          body : Block.t; }
    | VStruct of
        { fields : (string * value) list; }
    | VHeader of
        { fields : (string * value) list;
          is_valid : bool }
    | VUnion of
        { fields : (string * value) list; }
    | VStack of
        { headers : value list;
          size : Bigint.t;
          next : Bigint.t; }
    | VEnumField of
        { typ_name : string;
          enum_name : string; }
    | VSenumField of
        { typ_name : string;
          enum_name : string;
          v : value; }
    | VSenum of (string * value) list
    | VRuntime of
        { loc : loc;
          obj_name : string; }
    | VParser of vparser
    | VControl of vcontrol
    | VPackage of
        { params : Parameter.t list;
          args : (string * loc) list; }
    | VTable of vtable
    | VExternFun of
        { name : string;
          caller : (loc * string) option;
          params : Typed.Parameter.t list; }
    | VExternObj of (string * Parameter.t list) list
    [@@deriving sexp,show,yojson]

  and vparser = {
    pscope : Env.EvalEnv.t;
    pconstructor_params : Parameter.t list;
    pparams : Typed.Parameter.t list;
    plocals : Declaration.t list;
    states : Parser.state list;
  }
  [@@deriving sexp,show,yojson]

  and vcontrol = {
    cscope : Env.EvalEnv.t;
    cconstructor_params : Parameter.t list;
    cparams : Typed.Parameter.t list;
    clocals : Declaration.t list;
    apply : Block.t;
  }
  [@@deriving sexp,show,yojson]

  and vtable = {
    name : string;
    keys : Table.pre_key list;
    actions : Table.action_ref list;
    default_action : Table.action_ref;
    const_entries : Table.pre_entry list;
  }
  [@@deriving sexp,show,yojson]

  and pre_lvalue =
    | LName of
      { name : Types.name; }
    | LMember of
      { expr : lvalue;
        name : string; }
    | LBitAccess of
        { expr : lvalue;
          msb : Util.bigint;
          lsb : Util.bigint; }
    | LArrayAccess of
        { expr : lvalue;
          idx : value; }
  [@@deriving sexp,show,yojson]

  and lvalue = {
    lvalue : pre_lvalue;
    typ : Type.t
  }
  [@@deriving sexp,show,yojson]

  and set =
    | SSingleton of
        { w : Bigint.t;
          v : Bigint.t; }
    | SUniversal
    | SMask of
        { v : value;
          mask : value; }
    | SRange of
        { lo : value;
          hi : value; }
    | SProd of set list
    | SLpm of
        { w : value;
          nbits : Bigint.t;
          v : value; }
    | SValueSet of
        { size : value;
          members : Match.t list list;
          sets : set list; }
  [@@deriving sexp,show,yojson]

  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject of string
  [@@deriving sexp,show,yojson]

  val assert_bool : value -> bool

  val assert_rawint : value -> Bigint.t

  val assert_bit : value -> Bigint.t * Bigint.t

  val assert_int : value -> Bigint.t * Bigint.t

  val bigint_of_val : value -> Bigint.t

  val assert_varbit : value -> Bigint.t * Bigint.t * Bigint.t

  val assert_string : value -> string

  val assert_tuple : value -> value list

  val assert_set : value -> Bigint.t -> set

  val assert_error : value -> string

  val assert_fun : value -> Env.EvalEnv.t * Typed.Parameter.t list * Block.t

  val assert_builtin : value -> string * lvalue

  val assert_action : value -> Env.EvalEnv.t * Typed.Parameter.t list * Block.t

  val assert_struct : value -> (string * value) list

  val assert_header : value -> (string * value) list * bool

  val assert_union : value -> (string * value) list

  val assert_stack : value -> value list * Bigint.t * Bigint.t

  val assert_enum_field : value -> string * string

  val assert_senum_field : value -> string * string * value

  val assert_senum : value -> (string * value) list

  val assert_runtime : value -> loc

  val assert_parser : value -> vparser

  val assert_control : value -> vcontrol

  val assert_package : value -> Parameter.t list * (string * loc) list

  val assert_table : value -> vtable

  val assert_externfun : value -> Parameter.t list

  val assert_externobj : value -> (string * Parameter.t list) list

  val assert_lname : lvalue -> Types.name

  val assert_lmember : lvalue -> lvalue * string

  val assert_lbitaccess : lvalue -> lvalue * Util.bigint * Util.bigint

  val assert_larrayaccess : lvalue -> lvalue * value

  val assert_singleton : set -> Bigint.t * Bigint.t

  val assert_mask : set -> value * value

  val assert_range : set -> value * value

  val assert_prod : set -> set list

  val assert_lpm : set -> value * Bigint.t * value

  val assert_valueset : set -> value * Match.t list list * set list

  val assert_action_decl : Declaration.t -> Typed.Parameter.t list

end = struct
  type buf = Cstruct_sexp.t [@@deriving sexp]
  let buf_to_yojson b = failwith "unimplemented"
  let buf_of_yojson j = failwith "unimplemented"
  let pp_buf fmt buf = Format.pp_print_string fmt "<buf>"
  let show_buf buf = "<buf>"

  type pkt = {
    emitted : buf;
    main : buf;
    in_size : int;
  } [@@deriving sexp,show,yojson]

  type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list * (Ast.qualified_name * Ast.action list) list

  type vsets = Match.t list list

  type ctrl = entries * vsets

  type loc = string [@@deriving sexp, show,yojson]

  type value =
    (* | VLoc of loc *)
    | VNull
    | VBool of bool
    | VInteger of Util.bigint
    | VBit of
        { w : Util.bigint;
          v : Util.bigint; }
    | VInt of
        { w : Util.bigint;
          v : Util.bigint; }
    | VVarbit of
        { max : Util.bigint;
          w : Util.bigint;
          v : Util.bigint; }
    | VString of string
    | VTuple of value list
    | VRecord of (string * value) list
    | VSet of set
    | VError of string
    | VMatchKind of string
    | VFun of
        { scope : Env.EvalEnv.t;
          params : Typed.Parameter.t list;
          body : Block.t; }
    | VBuiltinFun of
        { name : string;
          caller : lvalue; }
    | VAction of
        { scope : Env.EvalEnv.t;
          params : Typed.Parameter.t list;
          body : Block.t; }
    | VStruct of
        { fields : (string * value) list; }
    | VHeader of
        { fields : (string * value) list;
          is_valid : bool }
    | VUnion of
        { fields : (string * value) list; }
    | VStack of
        { headers : value list;
          size : Util.bigint;
          next : Util.bigint; }
    | VEnumField of
        { typ_name : string;
          enum_name : string; }
    | VSenumField of
        { typ_name : string;
          enum_name : string;
          v : value; }
    | VSenum of (string * value) list
    | VRuntime of
        { loc : loc;
          obj_name : string; }
    | VParser of vparser
    | VControl of vcontrol
    | VPackage of
        { params : Parameter.t list;
          args : (string * loc) list; }
    | VTable of vtable
    | VExternFun of
        { name : string;
          caller : (loc * string) option;
          params : Typed.Parameter.t list; }
    | VExternObj of (string * Parameter.t list) list
  [@@deriving sexp, show,yojson]

  and vparser = {
    pscope : Env.EvalEnv.t;
    pconstructor_params : Parameter.t list;
    pparams : Typed.Parameter.t list;
    plocals : Declaration.t list;
    states : Parser.state list;
  }
  [@@deriving sexp,show,yojson]

  and vcontrol = {
    cscope : Env.EvalEnv.t;
    cconstructor_params : Parameter.t list;
    cparams : Typed.Parameter.t list;
    clocals : Declaration.t list;
    apply : Block.t;
  }
  [@@deriving sexp,show,yojson]

  and vtable = {
    name : string;
    keys : Table.pre_key list;
    actions : Table.action_ref list;
    default_action : Table.action_ref;
    const_entries : Table.pre_entry list;
  }
  [@@deriving sexp,show,yojson]

  and pre_lvalue =
    | LName of
      { name : Types.name; }
    | LMember of
      { expr : lvalue;
        name : string; }
    | LBitAccess of
        { expr : lvalue;
          msb : Util.bigint;
          lsb : Util.bigint; }
    | LArrayAccess of
        { expr : lvalue;
          idx : value; }
  [@@deriving sexp,show,yojson]

  and lvalue =
    { lvalue: pre_lvalue;
      typ: Typed.Type.t }
  [@@deriving sexp,show,yojson]

  and set =
    | SSingleton of
        { w : Util.bigint;
          v : Util.bigint; }
    | SUniversal
    | SMask of
        { v : value;
          mask : value; }
    | SRange of
        { lo : value;
          hi : value; }
    | SProd of set list
    | SLpm of
        { w : value;
          nbits : Util.bigint;
          v : value; }
    | SValueSet of
        { size : value;
          members : Match.t list list;
          sets : set list; }
  [@@deriving sexp,show,yojson]

  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject of string
  [@@deriving sexp,show,yojson]

  let assert_bool v =
    match v with
    | VBool b -> b
    | _ -> failwith "not a bool"

  let assert_rawint v =
    match v with
    | VInteger n -> n
    | _ -> failwith "not an variable-size integer"

  let rec assert_bit v =
    match v with
    | VBit{w;v} -> (w,v)
    | VSenumField{v;_} -> assert_bit v
    | _ -> raise_s [%message "not a bitstring" ~v:(v:value)]

  let assert_int v =
    match v with
    | VInt {w;v} -> (w,v)
    | _ -> failwith "not an int"

  let rec bigint_of_val v =
    match v with
    | VInt{v=n;_}
    | VBit{v=n;_}
    | VInteger n
    | VVarbit{v=n;_} -> n
    | VSenumField{v;_} -> bigint_of_val v
    | VBool b -> if b then Bigint.one else Bigint.zero
    | _ -> failwith "value not representable as bigint"

  let assert_varbit v =
    match v with
    | VVarbit {max;w;v} -> (max,w,v)
    | _ -> failwith "not a varbit"

  let assert_string v =
    match v with
    | VString s -> s
    | _ -> failwith "not a string"

  let assert_tuple v =
    match v with
    | VTuple l -> l
    | _ -> failwith "not a tuple"

  let rec assert_set v w =
    match v with
    | VSet s -> s
    | VInteger i -> SSingleton{w;v=i}
    | VInt {v=i;_} -> SSingleton{w;v=i}
    | VBit{v=i;_} -> SSingleton{w;v=i}
    | VSenumField{v;_} -> assert_set v w
    | VEnumField _ -> failwith "enum field not a set"
    | _ -> failwith "not a set"

  let assert_error v =
    match v with
    | VError s -> s
    | _ -> failwith "not an error"

  let assert_fun v =
    match v with
    | VFun {scope;params;body} -> (scope,params,body)
    | _ -> failwith "not a function"

  let assert_builtin v =
    match v with
    | VBuiltinFun {name; caller} -> name, caller
    | _ -> failwith "not a builtin function"

  let assert_action v =
    match v with
    | VAction {scope;params;body} -> (scope, params, body)
    | _ -> failwith "not an action"

  let assert_struct v =
    match v with
    | VStruct {fields;_} -> fields
    | _ -> failwith "not a struct"

  let assert_header v =
    match v with
    | VHeader {fields;is_valid;_} -> fields, is_valid
    | _ -> failwith "not a header"

  let assert_union v =
    match v with
    | VUnion {fields} -> fields
    | _ -> failwith "not a union"

  let assert_stack v =
    match v with
    | VStack {headers;size;next} -> (headers, size, next)
    | _ -> failwith "not a stack"

  let assert_enum_field v =
    match v with
    | VEnumField {typ_name;enum_name} -> (typ_name, enum_name)
    | _ -> failwith "not an enum field"

  let assert_senum_field v =
    match v with
    | VSenumField {typ_name;enum_name;v} -> (typ_name, enum_name, v)
    | _ -> failwith "not an senum field"

  let assert_senum v =
    match v with
    | VSenum l -> l
    | _ -> failwith "not an senum"

  let assert_runtime v =
    match v with
    | VRuntime {loc; _ } -> loc
    | _ -> failwith "not a runtime value"

  let assert_parser v =
    match v with
    | VParser p -> p
    | _ -> failwith "not a parser"

  let assert_control v =
    match v with
    | VControl c -> c
    | _ -> failwith "not a control"

  let assert_package v =
    match v with
    | VPackage {params;args} -> (params, args)
    | _ -> failwith "not a package"

  let assert_table v =
    match v with
    | VTable t -> t
    | _ -> failwith "not a table"

  let assert_externfun v =
    match v with
    | VExternFun {params;_} -> params
    | _ -> failwith "not an extern function"

  let assert_externobj v =
    match v with
    | VExternObj l -> l
    | _ -> failwith "not an extern object"

  let assert_lname l =
    match l.lvalue with
    | LName {name; _} -> name
    | _ -> failwith "not an lvalue name"

  let assert_lmember l =
    match l.lvalue with
    | LMember {expr; name; _} -> (expr, name)
    | _ -> failwith "not an lvalue member"

  let assert_lbitaccess l =
    match l.lvalue with
    | LBitAccess {expr; msb; lsb; _} -> (expr, msb, lsb)
    | _ -> failwith "not an lvalue bitaccess"

  let assert_larrayaccess l =
    match l.lvalue with
    | LArrayAccess {expr; idx; _} -> (expr, idx)
    | _ -> failwith "not an lvalue array access"

  let assert_singleton s =
    match s with
    | SSingleton {w; v} -> (w,v)
    | _ -> failwith "not a singleton set"

  let assert_mask s =
    match s with
    | SMask {v;mask} -> (v,mask)
    | _ -> failwith "not a mask set"

  let assert_range s =
    match s with
    | SRange{lo;hi} -> (lo,hi)
    | _ -> failwith "not a range set"

  let assert_prod s =
    match s with
    | SProd l -> l
    | _ -> failwith "not a product set"

  let assert_lpm s =
    match s with
    | SLpm {w; nbits; v} -> (w,nbits,v)
    | _ -> failwith "not an lpm set"

  let assert_valueset s =
    match s with
    | SValueSet {size; members; sets} -> (size, members, sets)
    | _ -> failwith "not a valueset"

  let assert_action_decl (d : Declaration.t) : Typed.Parameter.t list =
    match snd d with
    | Action {data_params;ctrl_params;_} -> data_params @ ctrl_params
    | _ -> failwith "not an action declaration"

end

and Env : sig

  exception BadEnvironment of string
  exception UnboundName of string
  val raise_unbound : Types.name -> unit

  module EvalEnv : sig
    type t [@@deriving sexp,show,yojson]

    val empty_eval_env : t

    val get_toplevel : t -> t
    val get_val_firstlevel : t -> (string * Value.loc) list

    val get_namespace : t -> string
    val set_namespace : string -> t -> t

    val insert_val_bare : string -> Value.loc -> t -> t
    val insert_typ_bare : string -> Type.t -> t -> t

    val insert_val : Types.name -> Value.loc -> t -> t
    val insert_typ : Types.name -> Type.t -> t -> t

    val insert_vals_bare : (string * Value.loc) list -> t -> t
    val insert_typs_bare : (string * Type.t) list -> t -> t

    val insert_vals : (Types.name * Value.loc) list -> t -> t
    val insert_typs : (Types.name * Type.t) list -> t -> t

    val find_val : Types.name -> t -> Value.loc
    val find_val_opt : Types.name -> t -> Value.loc option
    val find_typ : Types.name -> t -> Type.t

    val push_scope : t -> t
    val pop_scope : t -> t

    val print_env : t -> unit
  end

  module Renamer : sig
    type t [@@deriving sexp,show,yojson]
    val create : unit -> t
    val seen_name : t -> string -> bool
    val observe_name : t -> string -> unit
    val freshen_name : t -> string -> string
  end

  module CheckerEnv : sig
    type t [@@deriving sexp,show,yojson]

    val empty_t : unit -> t
    val empty_with_renamer : Renamer.t -> t

    val renamer : t -> Renamer.t

    val resolve_type_name_opt : Types.name -> t -> Typed.Type.t option
    val resolve_type_name : Types.name -> t -> Typed.Type.t
    val find_type_of_opt : Types.name -> t -> (Typed.Type.t * Typed.direction) option
    val find_type_of : Types.name -> t -> Typed.Type.t * Typed.direction
    val find_types_of : Types.name -> t -> (Typed.Type.t * Typed.direction) list
    val find_const : Types.name -> t -> Value.value
    val find_const_opt : Types.name -> t -> Value.value option
    val find_extern_opt : Types.name -> t -> Typed.ExternMethods.t option
    val find_extern : Types.name -> t -> Typed.ExternMethods.t

    val insert_type : Types.name -> Typed.Type.t -> t -> t
    val insert_types : (string * Typed.Type.t) list -> t -> t
    val insert_type_of : Types.name -> Typed.Type.t -> t -> t
    val insert_dir_type_of : Types.name -> Typed.Type.t -> Typed.direction -> t -> t
    val insert_type_var : Types.name -> t -> t
    val insert_type_vars : string list -> t -> t
    val insert_const : Types.name -> Value.value -> t -> t
    val insert_extern : Types.name -> Typed.ExternMethods.t -> t -> t
    val push_scope : t -> t
    val pop_scope : t -> t

    val eval_env_of_t : t -> EvalEnv.t
  end

end = struct

  open Sexplib.Conv
  (* module Info = I *)

  exception BadEnvironment of string
  exception UnboundName of string

  let raise_unbound (name: Types.name) =
    let str_name =
      match name with
      | Types.QualifiedName (qs, name) ->
         qs @ [name]
         |> List.map ~f:snd
         |> String.concat ~sep:"."
      | Types.BareName name ->
         snd name
    in
    raise (UnboundName str_name)

  type 'binding env = (string * 'binding) list list [@@deriving sexp,show,yojson]

  let push (env: 'a env) : 'a env = [] :: env

  let no_scopes () =
    raise (BadEnvironment "no scopes")

  let pop: 'a env -> 'a env = function
    | []        -> no_scopes ()
    | _ :: env' -> env'

  let split_at name scope =
    let rec split_at' seen scope =
    match scope with
    | [] -> None
    | (x, value) :: rest ->
       if x = name
       then Some (seen, (x, value), rest)
       else split_at' (seen @ [x, value]) rest
    in
    split_at' [] scope

  let update_in_scope name value scope =
    match split_at name scope with
    | None -> None
    | Some (xs, _, ys) ->
       Some (xs @ (name, value) :: ys)

  let insert_bare name value env =
    match env with
    | [] -> no_scopes ()
    | h :: t -> ((name, value) :: h) :: t

  let rec update_bare name value env =
    match env with
    | [] -> no_scopes ()
    | inner_scope :: scopes ->
       match update_in_scope name value inner_scope with
       | Some inner_scope -> Some (inner_scope :: scopes)
       | None ->
          match update_bare name value scopes with
          | Some env -> Some (inner_scope :: env)
          | None -> None

  let update_toplevel name value env =
    let (env0,env1) = List.split_n env (List.length env - 1) in
    match update_bare name value env1 with
    | Some env1' -> Some (env0 @ env1')
    | None -> None

  let insert_toplevel (name: string) (value: 'a) (env: 'a env) : 'a env =
    let (env0,env1) = List.split_n env (List.length env - 1) in
    let env1' = insert_bare name value env1 in
    env0 @ env1'

  let insert name value env =
    match name with
    | Types.BareName (_, name) -> insert_bare name value env
    | Types.QualifiedName ([], (_, name)) -> insert_toplevel name value env
    | _ -> failwith "unimplemented"

  let update name value env =
    match name with
    | Types.BareName (_, name) -> update_bare name value env
    | Types.QualifiedName ([], (_, name)) -> update_toplevel name value env
    | _ -> failwith "unimplemented"

  let rec find_bare_opt (name: string) : 'a env -> 'a option = function
    | [] -> None
    | h :: t ->
      let select (name', _) = name = name' in
      match List.find ~f:select h with
      | None              -> find_bare_opt name t
      | Some (_, binding) -> Some binding

  let rec find_all_bare (name: string) : 'a env -> 'a list = function
    | [] -> []
    | h :: t ->
       let select acc (name', value) =
         if name' = name
         then value :: acc
         else acc
       in
       List.fold h ~init:[] ~f:select @ find_all_bare name t

  let find_all name env =
    match name with
    | Types.BareName (_, name) -> find_all_bare name env
    | Types.QualifiedName ([], (_, n)) ->
       begin match List.last env with
       | Some top -> find_all_bare n [top]
       | None -> no_scopes ()
       end
    | _ -> failwith "unimplemented"

  let string_of_name = function
    | Types.BareName (_, n) -> n
    | _ -> ""

  let opt_to_exn name v =
    match v with
    | Some v -> v
    | None -> raise_unbound name

  let find_bare (name: string) (env: 'a env) : 'a =
    opt_to_exn (Types.BareName (Info.dummy, name)) (find_bare_opt name env)

  let find_toplevel (name: string) (env: 'a env) : 'a =
    match List.rev env with
    | []       -> no_scopes ()
    | env :: _ -> find_bare name [env]

  let find_toplevel_opt (name: string) (env: 'a env) : 'a option =
    match List.rev env with
    | []       -> None
    | env :: _ -> find_bare_opt name [env]

  let find (name: Types.name) (env: 'a env) : 'a =
    match name with
    | Types.BareName (_, n) -> find_bare n env
    | Types.QualifiedName ([], (_, n)) -> find_toplevel n env
    | _ -> failwith "unimplemented"

  let find_opt (name: Types.name) (env: 'a env) : 'a option =
    match name with
    | Types.BareName (_, n) -> find_bare_opt n env
    | Types.QualifiedName ([], (_, n)) -> find_toplevel_opt n env
    | _ -> failwith "unimplemented"

  let empty_env : 'a env = [[]]

  module EvalEnv = struct
    type t = {
      (* maps variables to their locations in memory (state) *)
      vs : Value.loc env;
      (* map variables to their types; only needed in a few cases *)
      typ : Type.t env;
      (* dynamically maintain the control-plane namespace *)
      namespace : string;
    }
    [@@deriving sexp,show,yojson]

    let empty_eval_env = {
      vs = [[]];
      typ = [[]];
      namespace = "";
    }

    let get_val_firstlevel (env: t) =
      match env.vs with
      | scope :: rest -> scope
      | [] -> no_scopes ()

    let get_toplevel (env : t) : t =
      let get_last l =
        match List.rev l with
        | [] -> raise (BadEnvironment "no toplevel")
        | h :: _ -> [h] in
      {vs = get_last env.vs;
       typ = get_last env.typ;
       namespace = "";}

    let get_val_firstlevel env =
      List.hd_exn (env.vs)

    let get_namespace env =
      env.namespace

    let set_namespace name env =
      {env with namespace = name}

    let insert_val name binding e =
      {e with vs = insert name binding e.vs}

    let insert_val_bare name binding e =
      {e with vs = insert (Types.BareName (Info.dummy, name)) binding e.vs}

    let insert_typ name binding e =
      {e with typ = insert name binding e.typ}

    let insert_typ_bare name =
      insert_typ (Types.BareName (Info.dummy, name))

    let insert_vals bindings e =
      List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_val b c a)

    let fix_bindings bindings =
      List.map bindings
        ~f:(fun (name, v) -> Types.BareName (Info.dummy, name), v)

    let insert_vals_bare bindings =
      insert_vals (fix_bindings bindings)

    let insert_typs bindings e =
      List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_typ b c a)

    let insert_typs_bare bindings =
      insert_typs (fix_bindings bindings)

    let find_val name e =
      find name e.vs

    let find_val_opt name e =
      find_opt name e.vs

    let find_typ name e =
      find name e.typ

    let push_scope (e : t) : t =
      {vs = push e.vs;
       typ = push e.typ;
       namespace = e.namespace;}

    let pop_scope (e:t) : t =
      {vs = pop e.vs;
       typ = pop e.typ;
       namespace = e.namespace;}

    (* TODO: for the purpose of testing expressions and simple statements only*)
    let print_env (e:t) : unit =
      let open Core_kernel in
      print_endline "First environment value mappings:";
      let f (name, value) =
        print_string "     ";
        print_string name;
        print_string " -> ";
        (* let open Value in *)
        let vstring = "" in
          (* match value with
          | VNull -> "null"
          | VBool b -> string_of_bool b
          | VInteger v
          | VBit {v;_}
          | VInt {v;_}
          | VVarbit {v;_} -> begin match Bigint.to_int v with
              | None -> "<bigint>"
              | Some n -> string_of_int n end
          | VString s -> s
          | VTuple _ -> "<tuple>"
          | VRecord _ -> "<record>"
          | VSet _ -> "<set>"
          | VError s -> "Error: " ^ s
          | VMatchKind s -> "Match Kind: " ^ s
          | VFun _ -> "<function>"
          | VBuiltinFun _ -> "<function>"
          | VAction _ -> "<action>"
          | VStruct {fields;_} -> "<struct>"
            (* List.iter fields ~f:(fun a -> print_string "    "; f a); "" *)
          | VHeader {fields;is_valid;_} ->
            "<header> with " ^ (string_of_bool is_valid)
            (* List.iter fields ~f:(fun a -> print_string "    "; f a); "" *)
          | VUnion {fields} -> "<union>"
            (* List.iter fields ~f:(fun a -> print_string "    "; f a); "" *)
          | VStack _ -> "<stack>"
          | VEnumField{typ_name;enum_name} -> typ_name ^ "." ^ enum_name
          | VSenumField{typ_name;enum_name;_} -> typ_name ^ "." ^ enum_name ^ " <value>"
          | VRuntime r -> "<location>"
          | VParser _ -> "<parser>"
          | VControl _ -> "<control>"
          | VPackage _ -> "<package>"
          | VTable _ -> "<table>"
          | VExternFun _ -> "<function>" in *)
        print_endline vstring in
      match e.vs with
      | [] -> ()
      | h :: _ -> h |> List.rev |> List.iter ~f:f

  end

  module Renamer = struct
    type state = { counter : int;
                   seen : string list }
    [@@deriving sexp,show,yojson]
    type t = state ref
    [@@deriving sexp,show,yojson]

    let create () = ref { counter = 0; seen = [] }

    let seen_name st name =
      List.mem ~equal:String.equal !st.seen name

    let observe_name st name =
      if seen_name st name
      then ()
      else st := { !st with seen = name :: !st.seen }

    let incr st =
      st := {!st with counter = !st.counter + 1}

    let rec gen_name st name =
      let { counter = i; _ } = !st in
      let new_name = Printf.sprintf "%s%d" name i in
      incr st;
      if seen_name st new_name
      then gen_name st name
      else new_name

    let freshen_name st name =
      let new_name =
        if seen_name st name
        then gen_name st name
        else name
      in
      observe_name st new_name;
      new_name

  end

  module CheckerEnv = struct

    type t =
      { (* types that type names refer to (or Typevar for vars in scope) *)
        typ: Typed.Type.t env;
        (* maps variables to their types & directions *)
        typ_of: (Typed.Type.t * Typed.direction) env;
        (* maps constants to their values *)
        const: Value.value env;
        (* Extern methods *)
        externs: ExternMethods.t env;
        (* for generating fresh type variables *)
        renamer: Renamer.t }
    [@@deriving sexp,show,yojson]

    let empty_with_renamer r : t =
      { typ = empty_env;
        typ_of = empty_env;
        const = empty_env;
        externs = empty_env;
        renamer = r }

    let empty_t () : t =
      empty_with_renamer @@ Renamer.create ()

    let renamer env =
      env.renamer

    let resolve_type_name_opt name env =
      find_opt name env.typ

    let resolve_type_name (name: Types.name) env =
      opt_to_exn name (resolve_type_name_opt name env)

    let find_type_of_opt name env =
      find_opt name env.typ_of

    let find_type_of name env =
      opt_to_exn name (find_type_of_opt name env)

    let find_types_of name env =
      find_all name env.typ_of

    let find_const name env =
      find name env.const

    let find_const_opt name env =
      find_opt name env.const

    let find_extern_opt name env =
      find_opt name env.externs

    let find_extern name env =
      opt_to_exn name (find_extern_opt name env)

    let insert_type name typ env =
      { env with typ = insert name typ env.typ }

    let insert_types names_types env =
      let go env (name, typ) =
        insert_type (Types.BareName (Info.dummy, name)) typ env
      in
      List.fold ~f:go ~init:env names_types

    let insert_type_var var env =
      { env with typ = insert var (Typed.Type.TypeName var) env.typ }

    let insert_type_vars vars env =
      let go env var =
        insert_type_var (Types.BareName (Info.dummy, var)) env
      in
      List.fold ~f:go ~init:env vars

    let insert_type_of var typ env =
      { env with typ_of = insert var (typ, Typed.Directionless) env.typ_of }

    let insert_dir_type_of var typ dir env =
      { env with typ_of = insert var (typ, dir) env.typ_of }

    let insert_extern var extern env =
      { env with externs = insert var extern env.externs }

    let insert_const var value env =
      match find_const_opt var env with
      | Some _ -> raise_s [%message "constant already defined!"
                              ~name:(var:Types.name)]
      | None -> { env with const = insert var value env.const }

    let push_scope env =
      { typ = push env.typ;
        typ_of = push env.typ_of;
        const = push env.const;
        externs = push env.externs;
        renamer = env.renamer }

    let pop_scope env =
      { typ = pop env.typ;
        typ_of = pop env.typ_of;
        const = pop env.const;
        externs = push env.externs;
        renamer = env.renamer }

    let eval_env_of_t (cenv: t) : EvalEnv.t =
      { vs = [[]];
        typ = cenv.typ;
        namespace = "";}
  end


end

type program =
    Program of Declaration.t list [@name "program"]
   [@@deriving sexp,show,yojson]
