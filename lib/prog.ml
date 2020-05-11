open Util
open Core_kernel

open Typed

module P4Int = Types.P4Int

module P4String = Types.P4String

module rec TypeParameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: Typed.direction;
      typ: Typed.Type.t;
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
        params: TypeParameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list}
        [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        params: TypeParameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list}
    [@@deriving sexp,yojson]
    
  type t = pre_t info [@@deriving sexp,yojson]
end

and KeyValue : sig
  type pre_t = 
    { key : P4String.t;
      value : Expression.t } 
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t = 
    { key : P4String.t;
      value : Expression.t } 
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
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
  [@@deriving sexp,yojson]

  and typed_t = { expr: pre_t;
                  typ: Type.t;
                  dir: direction }
  and t = typed_t info [@@deriving sexp,yojson]
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
        [@@deriving sexp,yojson]

  and typed_t = { expr: pre_t;
                  typ: Type.t;
                  dir: direction }
  and t = typed_t info [@@deriving sexp,yojson]
end

and Match : sig
  type pre_t =
    DontCare
  | Expression of
      { expr: Expression.t }
  [@@deriving sexp,yojson { exn = true }]

  type typed_t = { expr: pre_t;
                   typ: Type.t }
  [@@deriving sexp,yojson { exn = true }]

  type t = typed_t info [@@deriving sexp,yojson { exn = true }]
end = struct
  type pre_t =
    DontCare
  | Expression of
      { expr: Expression.t }
  [@@deriving sexp,yojson { exn = true }]

  type typed_t = { expr: pre_t;
                   typ: Type.t }
  [@@deriving sexp,yojson { exn = true }]

  type t = typed_t info [@@deriving sexp,yojson { exn = true }]
end

and Table : sig
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: Types.name;
          args: (Expression.t option) list }
      [@@deriving sexp,yojson]

      type typed_action_ref =
        { action: pre_action_ref;
          typ: Typed.Type.t }
      [@@deriving sexp,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,yojson]

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
          name: Types.name;
          args: (Expression.t option) list }
      [@@deriving sexp,yojson]

      type typed_action_ref =
        { action: pre_action_ref;
          typ: Typed.Type.t }
      [@@deriving sexp,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,yojson]

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
        { annotations: Annotation.t list;
          const: bool;
          name: Types.P4String.t;
          value: Expression.t }
      [@@deriving sexp,yojson]

      type property = pre_property info [@@deriving sexp,yojson]

      let name_of_property (_, {name; _}) =
        snd name
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
      [@@deriving sexp,yojson]

      and typed_t =
        { stmt: pre_t;
          typ: StmType.t }

      and t = typed_t info [@@deriving sexp,yojson]
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
  [@@deriving sexp,yojson]

  and typed_t =
    { stmt: pre_t;
      typ: StmType.t }
    
  and t = typed_t info [@@deriving sexp,yojson]
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
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
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
        data_params: TypeParameter.t list;
        ctrl_params: TypeParameter.t list;
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
        params: TypeParameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
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
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
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
        data_params: TypeParameter.t list;
        ctrl_params: TypeParameter.t list;
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
        params: TypeParameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: Types.P4String.t;
        type_params: Types.P4String.t list;
        params: TypeParameter.t list }
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

and Value : sig
  type buf = Cstruct_sexp.t [@@deriving sexp]
  (* let buf_to_yojson b = failwith "unimplemented"
  let buf_of_yojson j = failwith "unimplemented" *)

  type pkt = {
    emitted : buf;
    main : buf;
    in_size : int;
  } [@@deriving sexp,yojson]

  type entries = Table.pre_entry list

  type vsets = Match.t list list

  type ctrl = entries * vsets

  type loc = string [@@deriving sexp, yojson]

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
        { params : TypeParameter.t list;
          body : Block.t; }
    | VBuiltinFun of 
        { name : string;
          caller : lvalue; }
    | VAction of 
        { params : TypeParameter.t list;
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
    | VRuntime of 
        { loc : loc;
          obj_name : string; }
    | VParser of vparser
    | VControl of vcontrol
    | VPackage of 
        { decl : Declaration.t;
          args : (string * value) list; }
    | VTable of vtable
    | VExternFun of 
        { name : string;
          caller : (loc * string) option; }
    [@@deriving sexp,yojson]
  
  and vparser = {
    pvs : (string * value) list;
    pparams : TypeParameter.t list;
    plocals : Declaration.t list;
    states : Parser.state list;
  }
  [@@deriving sexp,yojson]
  
  and vcontrol = {
    cvs : (string * value) list;
    cparams : TypeParameter.t list;
    clocals : Declaration.t list;
    apply : Block.t;
  }
  [@@deriving sexp,yojson]
  
  and vtable = {
    name : string;
    keys : Table.pre_key list;
    actions : Table.action_ref list;
    default_action : Table.action_ref;
    const_entries : Table.pre_entry list;
  }
  [@@deriving sexp,yojson]
  
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
  [@@deriving sexp,yojson]

  and lvalue = {
    lvalue : pre_lvalue;
    typ : Type.t
  }
  [@@deriving sexp,yojson]

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
  [@@deriving sexp,yojson]
  
  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject of string
  [@@deriving sexp,yojson]

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

  val assert_fun : value -> TypeParameter.t list * Block.t

  val assert_builtin : value -> string * lvalue 

  val assert_action : value -> TypeParameter.t list * Block.t 

  val assert_struct : value -> (string * value) list 

  val assert_header : value -> (string * value) list * bool 

  val assert_union : value -> (string * value) list 

  val assert_stack : value -> value list * Bigint.t * Bigint.t 

  val assert_enum : value -> string * string 

  val assert_senum : value -> string * string * value 

  val assert_runtime : value -> loc

  val assert_parser : value -> vparser

  val assert_control : value -> vcontrol 

  val assert_package : value -> Declaration.t * (string * value) list 

  val assert_table : value -> vtable 

  val width_of_val : value -> Bigint.t

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

end = struct
  type buf = Cstruct_sexp.t [@@deriving sexp]
  let buf_to_yojson b = failwith "unimplemented"
  let buf_of_yojson j = failwith "unimplemented"

  type pkt = {
    emitted : buf;
    main : buf;
    in_size : int;
  } [@@deriving sexp,yojson]

  type entries = Table.pre_entry list

  type vsets = Match.t list list

  type ctrl = entries * vsets

  type loc = string [@@deriving sexp, yojson]
  type value =
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
        { params : TypeParameter.t list;
          body : Block.t; }
    | VBuiltinFun of 
        { name : string;
          caller : lvalue; }
    | VAction of 
        { params : TypeParameter.t list;
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
    | VRuntime of 
        { loc : loc;
          obj_name : string; }
    | VParser of vparser
    | VControl of vcontrol
    | VPackage of 
        { decl : Declaration.t;
          args : (string * value) list; }
    | VTable of vtable
    | VExternFun of
        { name : string;
          caller : (loc * string) option; }
  [@@deriving sexp, yojson]
  
  and vparser = {
    pvs : (string * value) list;
    pparams : TypeParameter.t list;
    plocals : Declaration.t list;
    states : Parser.state list;
  }
  [@@deriving sexp,yojson]
  
  and vcontrol = {
    cvs : (string * value) list;
    cparams : TypeParameter.t list;
    clocals : Declaration.t list;
    apply : Block.t;
  }
  [@@deriving sexp,yojson]
  
  and vtable = {
    name : string;
    keys : Table.pre_key list;
    actions : Table.action_ref list;
    default_action : Table.action_ref;
    const_entries : Table.pre_entry list;
  }
  [@@deriving sexp,yojson]
  
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
  [@@deriving sexp,yojson]

  and lvalue =
    { lvalue: pre_lvalue;
      typ: Typed.Type.t }
  [@@deriving sexp,yojson]

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
  [@@deriving sexp,yojson]
  
  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject of string
  [@@deriving sexp,yojson]

  let assert_bool v =
    match v with 
    | VBool b -> b 
    | _ -> failwith "not a bool"
  
  let assert_rawint v = 
    match v with 
    | VInteger n -> n 
    | _ -> failwith "not an variable-size integer"
  
  let assert_bit v = 
    match v with 
    | VBit{w;v} -> (w,v) 
    | _ -> raise_s [%message "not a bitstring" ~v:(v:value)]
  
  let assert_int v = 
    match v with 
    | VInt {w;v} -> (w,v)
    | _ -> failwith "not an int"

  let bigint_of_val v =
    match v with
    | VInt{v=n;_}
    | VBit{v=n;_}
    | VInteger n 
    | VVarbit{v=n;_} -> n
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
  
  let assert_set v w = 
    match v with
    | VSet s -> s 
    | VInteger i -> SSingleton{w;v=i}
    | VInt {v=i;_} -> SSingleton{w;v=i}
    | VBit{v=i;_} -> SSingleton{w;v=i}
    | _ -> failwith "not a set"
  
  let assert_error v =
    match v with 
    | VError s -> s
    | _ -> failwith "not an error"
  
  let assert_fun v =
    match v with 
    | VFun {params;body} -> (params,body)
    | _ -> failwith "not a function"
  
  let assert_builtin v =
    match v with 
    | VBuiltinFun {name; caller} -> name, caller
    | _ -> failwith "not a builtin function"
  
  let assert_action v = 
    match v with 
    | VAction {params;body} -> (params, body)
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
  
  let assert_enum v = 
    match v with 
    | VEnumField {typ_name;enum_name} -> (typ_name, enum_name)
    | _ -> failwith "not an enum field"
  
  let assert_senum v = 
    match v with 
    | VSenumField {typ_name;enum_name;v} -> (typ_name, enum_name, v)
    | _ -> failwith "not an senum field"
  
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
    | VPackage {decl;args} -> (decl, args) 
    | _ -> failwith "not a package"
  
  let assert_table v = 
    match v with 
    | VTable t -> t 
    | _ -> failwith "not a table"

  let rec width_of_val v =
    let field_width (name, value) =
      width_of_val value
    in
    match v with
    | VBit {w;_}
    | VInt {w;_}
    | VVarbit{w;_} ->
       w
    | VNull ->
       Bigint.zero
    | VBool _ ->
       Bigint.one
    | VStruct {fields}
    | VHeader {fields; _} ->
       fields
       |> List.map ~f:field_width
       |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
    | VSenumField {v; _} ->
       width_of_val v
    | VInteger _ -> failwith "width of VInteger"
    | VUnion _ -> failwith "width of header union unimplemented"
    | _ -> raise_s [%message "width of type unimplemented" ~v:(v: Value.value)]
  
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

end


type program =
    Program of Declaration.t list [@name "program"]

