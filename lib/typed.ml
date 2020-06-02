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

module rec Parameter : sig
  type t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t }
  [@@deriving sexp,yojson]
end = struct
  type t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t }
  [@@deriving sexp,yojson]
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

and NewType : sig
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp,yojson]
end = struct
  type t =
    { name: string;
      typ: Type.t }
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
    { name: string;
      typ: Type.t option;
      (* TODO remove this *)
      members: string list; }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { name: string;
      typ: Type.t option;
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

and ConstructorType : sig
  type t =
    { type_params: string list;
      parameters: ConstructParam.t list;
      return: Type.t }
    [@@deriving sexp,yojson]
end = struct
  type t =
    { type_params: string list;
      parameters: ConstructParam.t list;
      return: Type.t }
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

    (* Struct initializers *)
    | Record of RecordType.t

    (* set<t> *)
    | Set of t

    (* General error type *)
    | Error

    (* match_kind *)
    | MatchKind

    (* References to other types, including top level types *)
    | TypeName of Types.name

    (* "Opaque" type introduced by newtype *)
    | NewType of NewType.t

    (* P4 void (acts like unit) *)
    | Void

    (* header { l1: t1, ..., ln : tn } *)
    | Header of RecordType.t

    (* header union {11 : h1, ..., ln : hn} *)
    | HeaderUnion of RecordType.t

    (* struct { l1: t1, ..., ln : tn } *)
    | Struct of RecordType.t

    (* enum X { l1, ..., ln } *)
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

    | Constructor of ConstructorType.t

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

  (* Struct initializers *)
  | Record of RecordType.t

  (* set<t> *)
  | Set of t

  (* General error type *)
  | Error

  (* match_kind *)
  | MatchKind

  (* References to other types, including top level types *)
  | TypeName of Types.name

  (* "Opaque" type introduced by newtype *)
  | NewType of NewType.t

  (* P4 void (acts like unit) *)
  | Void

  (* header { l1: t1, ..., ln : tn } *)
  | Header of RecordType.t

  (* header union {11 : h1, ..., ln : hn} *)
  | HeaderUnion of RecordType.t

  (* struct { l1: t1, ..., ln : tn } *)
  | Struct of RecordType.t

  (* enum X { l1, ..., ln } *)
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

  | Constructor of ConstructorType.t

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

and StmtContext : sig
  type t =
  | Function of Type.t
  | Action
  | ParserState
  | ApplyBlock
  [@@deriving sexp,yojson]
end = struct
  type t =
  | Function of Type.t
  | Action
  | ParserState
  | ApplyBlock
  [@@deriving sexp,yojson]
end

and DeclContext : sig
  type t =
  | TopLevel
  | Nested
  | Statement of StmtContext.t
  [@@deriving sexp,yojson]
end = struct
  type t =
  | TopLevel
  | Nested
  | Statement of StmtContext.t
  [@@deriving sexp,yojson]
end

module ParamContext = struct
  type decl =
  | Parser
  | Control
  | Method
  | Action
  | Function
  | Package

  type t =
  | Runtime of decl
  | Constructor of decl
end
