type direction =
  | In
  | Out
  | InOut
  | Directionless

module rec Parameter : sig
  type t =
    { name: string;
      typ: Type.t;
      direction: direction}
end = struct
  include Parameter
end

and ConstructParam : sig
  type t =
    { name: string;
      typ: Type.t}
end = struct
  include ConstructParam
end

and PackageType : sig
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
end = struct
  include PackageType
end

and ControlType : sig
  type t = {type_params: string list;
            parameters: Parameter.t list}
end = struct
  include ControlType
end

and IntType : sig
  type t =
    { width: int }
end = struct
  include IntType
end

and ArrayType : sig
  type t =
    { typ: Type.t;
      size: int; }
end = struct
  include ArrayType
end

and TupleType : sig
  type t =
    { types: Type.t list }
end = struct
  include TupleType
end

and RecordType : sig
  type field =
    { name: string;
      typ: Type.t; }

  type t =
    { fields: field list; }
end = struct
  include RecordType
end

and EnumType : sig
  type t =
    { typ: Type.t option;
      members: string list; }
end = struct
  include EnumType
end

and FunctionType : sig
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
end = struct
  include FunctionType
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

  | Package of PackageType.t

  | Control of ControlType.t

  | Parser of ControlType.t

  (* <return type> <function name>(x1,...,xn) {...} *)
  | Function of FunctionType.t
end = struct
  include Type
end

module rec StmType : sig
  type t =
  | Unit
  | Void
end = struct
  include StmType
end
