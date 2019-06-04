type direction = In | Out | InOut (* If direction is not specified
                                   * then it is In. *)

module rec Parameter : sig
  type t =
    { name: string;
      typ: ExpType.t;
      direction: direction}
end = struct
  include Parameter
end

and ConstructParam : sig
  type t =
    { name: string;
      typ: ExpType.t;}
end = struct
  include ConstructParam
end

and DeclType : sig
  type t =
  (* header { l1: t1, ..., ln : tn } *)
  | Header of RecordType.t

  (* header union {11 : h1, ..., ln : hn}, hi is a Header Type *)
  | HeaderUnion of UnionType.t

  (* struct { l1: t1, ..., ln : tn } *)
  | Struct of RecordType.t

  (* enum { l1, ..., ln } *)
  | Enum of EnumType.t

  (* error *)
  | Error of string list

  (* match_kind *)
  | MatchKind of string list

  | Package of PackageType.t

  | Control of TypeDecl.t

  | Parser of TypeDecl.t

  (* <return type> <function name>(x1,...,xn) {...} *)
  | Function of FunctionType.t
  (* need to keep track of body *)
end = struct
  include DeclType
end

and PackageType : sig
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
end = struct
  include PackageType
end

and TypeDecl : sig
  type t = {type_params: string list;
            parameters: Parameter.t list}
(*  need to keep track of body  *)
end = struct
  include TypeDecl
end

and ExpType : sig
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
  | Var of IntType.t

  (* t[size] *)
  | Array of ArrayType.t

  (* (t1, ..., tn) *)
  | Tuple of TupleType.t

  (* set<t> *)
  | Set of t

  (* Type name *)
  | Name of string

  (* General error type *)
  | Error

  | TypeVar of string (* will also be used to access, indirectly DeclTypes...maybe...not yet *)

  | Void
end = struct
  include ExpType
end

and IntType : sig
  type t =
    { width: int }
end = struct
  include IntType
end

and ArrayType : sig
  type t =
    { typ: ExpType.t;
      size: int; }
end = struct
  include ArrayType
end

and TupleType : sig
  type t =
    { types: ExpType.t list }
end = struct
  include TupleType
end

and RecordType : sig
  type field =
    { name: string;
      typ: ExpType.t; }

  type t =
    { fields: field list; }
end = struct
  include RecordType
end

and EnumType : sig
  type t =
    { typ: ExpType.t option;
      fields: string list; }
end = struct
  include EnumType
end

and UnionType : sig
  type union_field =
    { name: string;
      h_type : string} (* In the environment h_type must
                           * be associated with a Header variant. *)
  type t =
    {union_fields : union_field list}
end = struct
  include UnionType
end

and FunctionType : sig
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: ExpType.t option} (* None represents a void function. *)
      (* TODO function return type can be void, a statement type, or an expression type *)
end = struct
  include FunctionType
end

module rec StmType : sig
  type t =
  | Unit
  | Void
end = struct
  include StmType
end
