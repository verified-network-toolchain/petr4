open Sexplib.Conv

type direction =
  | In
  | Out
  | InOut
  | Directionless
  [@@deriving sexp,yojson]

let eq_dir d1 d2 =
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless -> true
  | _ -> false

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

  val eq : t -> t -> bool
end = struct
  type t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: Types.P4String.t }
  [@@deriving sexp,yojson]

  let eq
    (* ignoring annotations for now... *)
    { direction=d1;
      typ=t1;
      variable=_,s1; _ }
    { direction=d2;
      typ=t2;
      variable=_,s2; _ } =
      eq_dir d1 d2 &&
      Type.eq t1 t2 &&
      Base.String.equal s1 s2
end

and ConstructParam : sig
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp, yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp, yojson]

  let eq
    { name=s1; typ=t1 }
    { name=s2; typ=t2 } =
    Base.String.equal s1 s2 && Type.eq t1 t2
end

and PackageType : sig
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
             [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t = {type_params: string list;
            parameters: ConstructParam.t list}
             [@@deriving sexp,yojson]

  let eq
    {type_params=t1; parameters=p1}
    {type_params=t2; parameters=p2} =
    Base.List.equal Base.String.equal t1 t2 &&
    Base.List.equal ConstructParam.eq p1 p2
end

and ControlType : sig
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t = {type_params: string list;
            parameters: Parameter.t list}
    [@@deriving sexp,yojson]

  let eq
    {type_params=s1; parameters=p1}
    {type_params=s2; parameters=p2} =
    Base.List.equal Base.String.equal s1 s2 &&
    Base.List.equal Parameter.eq p1 p2
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

  val eq : t -> t -> bool
end = struct
  type extern_method =
    { name: string;
      typ: FunctionType.t; }
    [@@deriving sexp,yojson]

  type t =
    { type_params: string list;
      methods: extern_method list }
    [@@deriving sexp,yojson]

  let eq_em
    { name=s1; typ=f1 }
    { name=s2; typ=f2 } =
    Base.String.equal s1 s2 &&
    FunctionType.eq f1 f2

  let eq
    { type_params=s1; methods=m1 }
    { type_params=s2; methods=m2 } =
    Base.List.equal Base.String.equal s1 s2 &&
    Base.List.equal eq_em m1 m2
end

and IntType : sig
  type t =
    { width: int }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { width: int }
    [@@deriving sexp,yojson]

  let eq {width=i1} {width=i2} = i1 = i2
end

and ArrayType : sig
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { typ: Type.t;
      size: int; }
    [@@deriving sexp,yojson]

  let eq { typ=t1; size=s1 } { typ=t2; size=s2 } =
    Type.eq t1 t2 && s1 = s2
end

and TupleType : sig
  type t =
    { types: Type.t list }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { types: Type.t list }
    [@@deriving sexp,yojson]

  let eq { types=t1 } { types=t2 } =
    Base.List.equal Type.eq t1 t2
end

and NewType : sig
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp,yojson]

    val eq : t -> t -> bool
end = struct
  type t =
    { name: string;
      typ: Type.t }
  [@@deriving sexp,yojson]

  let eq { name=s1; typ=t1 } { name=s2; typ=t2 } =
    Base.String.equal s1 s2 && Type.eq t1 t2
end

and RecordType : sig
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp,yojson]

  type t =
    { fields: field list; }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type field =
    { name: string;
      typ: Type.t; }
    [@@deriving sexp,yojson]

  type t =
    { fields: field list; }
    [@@deriving sexp,yojson]

  let eq_field
    { name=s1; typ=t1 }
    { name=s2; typ=t2 } =
    Base.String.equal s1 s2 && Type.eq t1 t2

  let eq { fields=f1 } { fields=f2 } =
    Base.List.equal eq_field f1 f2
end

and EnumType : sig
  type t =
    { name: string;
      typ: Type.t option;
      (* TODO remove this *)
      members: string list; }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { name: string;
      typ: Type.t option;
      members: string list; }
    [@@deriving sexp,yojson]

  let eq
    { name=s1; typ=t1; members=l1 }
    { name=s2; typ=t2; members=l2 } =
    Base.String.equal s1 s2 &&
    Util.eq_opt ~f:Type.eq t1 t2 &&
    Base.List.equal Base.String.equal l1 l2

end

and FunctionType : sig
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { type_params: string list;
      parameters: Parameter.t list;
      return: Type.t}
    [@@deriving sexp,yojson]

  let eq
    { type_params=s1; parameters=p1; return=t1}
    { type_params=s2; parameters=p2; return=t2} =
    Base.List.equal Base.String.equal s1 s2 &&
    Base.List.equal Parameter.eq p1 p2 &&
    Type.eq t1 t2
end

and SpecializedType : sig
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { base: Type.t;
      args: Type.t list; }
    [@@deriving sexp,yojson]

  let eq { base=b1; args=a1 } { base=b2; args=a2 } =
    Type.eq b1 b2 && Base.List.equal Type.eq a1 a2
end

and ActionType : sig
  type t =
    { data_params: Parameter.t list;
      ctrl_params: ConstructParam.t list}
      [@@deriving sexp,yojson]

   val eq : t -> t -> bool
end = struct
  type t =
  { data_params: Parameter.t list;
    ctrl_params: ConstructParam.t list}
      [@@deriving sexp,yojson]

   let eq
    { data_params=p1; ctrl_params=c1 }
    { data_params=p2; ctrl_params=c2 } =
    Base.List.equal Parameter.eq p1 p2 &&
    Base.List.equal ConstructParam.eq c1 c2
end

and ConstructorType : sig
  type t =
    { type_params: string list;
      parameters: ConstructParam.t list;
      return: Type.t }
    [@@deriving sexp,yojson]

   val eq : t -> t -> bool
end = struct
  type t =
    { type_params: string list;
      parameters: ConstructParam.t list;
      return: Type.t }
    [@@deriving sexp,yojson]

   let eq
     { type_params=s1; parameters=c1; return=t1}
     { type_params=s2; parameters=c2; return=t2} =
     Base.List.equal Base.String.equal s1 s2 &&
     Base.List.equal ConstructParam.eq c1 c2 &&
     Type.eq t1 t2
end

and TableType : sig
  type t = {result_typ_name:string}
  [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t = {result_typ_name:string}
  [@@deriving sexp,yojson]

  let eq {result_typ_name=s1} {result_typ_name=s2} =
    Base.String.equal s1 s2
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

    (* syntactic equality of types *)
    val eq : t -> t -> bool
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

  (* syntactic equality of types *)
  let rec eq t1 t2 =
    match t1, t2 with
    | Bool, Bool
    | String, String
    | Integer, Integer
    | Error, Error
    | MatchKind, MatchKind
    | Void, Void -> true
    | Int w1, Int w2
    | Bit w1, Bit w2
    | VarBit w1, VarBit w2 -> IntType.eq w1 w2
    | Array a1, Array a2 -> ArrayType.eq a1 a2
    | Tuple t1, Tuple t2
    | List t1, List t2 -> TupleType.eq t1 t2
    | Record r1, Record r2
    | Header r1, Header r2
    | HeaderUnion r1, HeaderUnion r2
    | Struct r1, Struct r2 -> RecordType.eq r1 r2
    | Set t1, Set t2 -> eq t1 t2
    | TypeName n1, TypeName n2 -> Types.name_eq n1 n2
    | NewType t1, NewType t2 -> NewType.eq t1 t2
    | Enum e1, Enum e2 -> EnumType.eq e1 e2
    | SpecializedType s1, SpecializedType s2
      -> SpecializedType.eq s1 s2
    | Package p1, Package p2 -> PackageType.eq p1 p2
    | Control c1, Control c2
    | Parser c1, Parser c2 -> ControlType.eq c1 c2
    | Extern e1, Extern e2 -> ExternType.eq e1 e2
    | Function f1, Function f2 -> FunctionType.eq f1 f2
    | Action a1, Action a2 -> ActionType.eq a1 a2
    | Constructor c1, Constructor c2 -> ConstructorType.eq c1 c2
    | Table t1, Table t2 -> TableType.eq t1 t2
    | _ -> false
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
