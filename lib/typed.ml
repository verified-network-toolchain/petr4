open Sexplib.Conv
type direction =
  | In
  | Out
  | InOut
  | Directionless
  [@@deriving sexp]

module rec Parameter : sig
  type t =
    { name: string;
      typ: Type.t;
      direction: direction}
    [@@deriving sexp]
end = struct
  type t =
    { name: string;
      typ: Type.t;
      direction: direction}
    [@@deriving sexp]
end

and ConstructParam : sig
  type t =
    { name: string;
      typ: Type.t}
    [@@deriving sexp]
end = struct
  type t =
    { name: string;
      typ: Type.t}
    [@@deriving sexp]
end

(* and ActionParam : sig
  type t 
    { name: string;
      typ: Type.t}
      [@@deriving sexp]
end = struct
  type t =
    { name: string;
      typ: Type.t}
      [@@deriving sexp]
end *)

and PackageType : sig
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
    [@@deriving sexp]
end = struct
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
    [@@deriving sexp]
end

and ControlType : sig
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp]
end = struct
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp]
end

and ExternType : sig
  type extern_method =
    { name: string;
      typ: FunctionType.t; }
    [@@deriving sexp]

  type t =
    { type_params: string list;
      methods: extern_method list }
    [@@deriving sexp]
end = struct
  type extern_method =
    { name: string;
      typ: FunctionType.t; }
    [@@deriving sexp]

  type t =
    { type_params: string list;
      methods: extern_method list }
    [@@deriving sexp]
end

and IntType : sig
  type t =
    { width: int }
    [@@deriving sexp]
end = struct
  type t =
    { width: int }
    [@@deriving sexp]
end

and ArrayType : sig
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp]
end = struct
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp]
end

and TupleType : sig
  type t =
    { types: Type.t list }
    [@@deriving sexp]
end = struct
  type t =
    { types: Type.t list }
    [@@deriving sexp]
end

and RecordType : sig
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp]

  type t =
    { fields: field list; }
    [@@deriving sexp]
end = struct
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp]

  type t =
    { fields: field list; }
    [@@deriving sexp]
end

and EnumType : sig
  type t =
    { typ: Type.t option;
      members: string list; }
    [@@deriving sexp]
end = struct
  type t =
    { typ: Type.t option;
      members: string list; }
    [@@deriving sexp]
end

and FunctionType : sig
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp]
end = struct
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp]
end

and SpecializedType : sig
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp]
end = struct
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp]
end

and ActionType : sig
  type t =
    { data_params: Parameter.t list;
      ctrl_params: ConstructParam.t list}
      [@@deriving sexp]
end = struct
  type t =
  { data_params: Parameter.t list;
    ctrl_params: ConstructParam.t list}
      [@@deriving sexp]
end

and TableType : sig
  type t = {result_typ_name:string}
  [@@deriving sexp]
end = struct
  type t = {result_typ_name:string}
  [@@deriving sexp]
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

  (* Type variables *)
  | TypeVar of string

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
  [@@deriving sexp]
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

  (* Type variables *)
  | TypeVar of string

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
  [@@deriving sexp]
end

module rec StmType : sig
  type t =
  | Unit
  | Void
  [@@deriving sexp]
end = struct
  type t =
  | Unit
  | Void
  [@@deriving sexp]
end
