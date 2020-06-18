open Util
open Core_kernel

module P4Int = Types.P4Int
module P4String = Types.P4String

module Op = Types.Op

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

module rec Parameter : sig
  type t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: P4String.t }
  [@@deriving sexp,yojson]

  val eq : t -> t -> bool
end = struct
  type t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: P4String.t }
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

and TypeParameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      direction: direction;
      typ: Type.t;
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and MethodPrototype : sig
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4String.t;
        params: TypeParameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list}
        [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4String.t;
        params: TypeParameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
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

  val eq : t -> t -> bool
end = struct
  type pre_t =
    { key : P4String.t;
      value : Expression.t }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]

  let eq (_,{ key=_,k1; value=v1 }) (_,{ key=_,k2; value=v2 }) =
    String.equal k1 k2 && Expression.eq v1 v2
end

and Annotation : sig
  type pre_body =
    | Empty
    | Unparsed of P4String.t list
    | Expression of Expression.t list
    | KeyValue of KeyValue.t list
  [@@deriving sexp,yojson]

  type body = pre_body info [@@deriving sexp,yojson]

  type pre_t =
    { name: P4String.t;
      body: body }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end = struct
  type pre_body =
    | Empty
    | Unparsed of P4String.t list
    | Expression of Expression.t list
    | KeyValue of KeyValue.t list
  [@@deriving sexp,yojson]

  type body = pre_body info [@@deriving sexp,yojson]

  type pre_t =
    { name: P4String.t;
      body: body }
  [@@deriving sexp,yojson]

  type t = pre_t info [@@deriving sexp,yojson]
end

and Expression : sig
  type pre_t =
    True
  | False
  | Int of P4Int.t
  | String of P4String.t
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
        name: P4String.t }
  | ErrorMember of P4String.t
  | ExpressionMember of
      { expr: t;
        name: P4String.t }
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

  (* syntactic equality of expressions *)
  val eq : t -> t -> bool
end = struct
  type pre_t =
    True
  | False
  | Int of P4Int.t
  | String of P4String.t
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
        name: P4String.t }
  | ErrorMember of P4String.t
  | ExpressionMember of
      { expr: t;
        name: P4String.t }
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

  (* syntactic equality of expressions *)
  let rec eq (_,{ expr=e1; _ }) (_,{ expr=e2; _ }) =
    match e1, e2 with
    | True,  True
    | False, False
    | DontCare, DontCare -> true
    | Int (_,{value=v1; width_signed=w1}),
      Int (_,{value=v2; width_signed=w2})
      -> Bigint.equal v1 v2
      && [%compare.equal: ((int * bool) option)] w1 w2
    | String (_,s1), String (_,s2)
      -> String.equal s1 s2
    | Name n1, Name n2
      -> Types.name_eq n1 n2
    | ArrayAccess { array=a1; index=i1 },
      ArrayAccess { array=a2; index=i2 }
      -> eq a1 a2 && eq i1 i2
    | BitStringAccess { bits=b1; lo=l1; hi=h1 },
      BitStringAccess { bits=b2; lo=l2; hi=h2 }
      -> eq b1 b2 && Bigint.equal l1 l2 && Bigint.equal h1 h2
    | List { values=v1 }, List { values=v2 }
      -> List.equal eq v1 v2
    | Record { entries=kv1 }, Record { entries=kv2 }
      -> List.equal KeyValue.eq kv1 kv2
    | UnaryOp { op=o1; arg=e1 }, UnaryOp { op=o2; arg=e2 }
      -> Op.eq_uni o1 o2 && eq e1 e2
    | BinaryOp { op=b1; args=(l1,r1) }, BinaryOp { op=b2; args=(l2,r2) }
      -> Op.eq_bin b1 b2 && eq l1 l2 && eq r1 r2
    | Cast { typ=t1; expr=e1 }, Cast { typ=t2; expr=e2 }
      -> Type.eq t1 t2 && eq e1 e2
    | TypeMember { typ=n1; name=_,s1 },
      TypeMember { typ=n2; name=_,s2 }
      -> Types.name_eq n1 n2 && String.equal s1 s2
    | ErrorMember (_,s1), ErrorMember (_,s2)
      -> String.equal s1 s2
    | ExpressionMember { expr=e1; name=_,s1 },
      ExpressionMember { expr=e2; name=_,s2 }
      -> eq e1 e2 && String.equal s1 s2
    | Ternary { cond=c1; tru=t1; fls=f1 },
      Ternary { cond=c2; tru=t2; fls=f2 }
      -> eq c1 c2 && eq t1 t2 && eq f1 f2
    | FunctionCall { func=e1; type_args=t1; args=l1 },
      FunctionCall { func=e2; type_args=t2; args=l2 }
      -> eq e1 e2 &&
        List.equal Type.eq t1 t2 &&
        List.equal begin Util.eq_opt ~f:eq end l1 l2
    | NamelessInstantiation { typ=t1; args=e1 },
      NamelessInstantiation { typ=t2; args=e2 }
      -> Type.eq t1 t2 && List.equal eq e1 e2
    | Mask { expr=e1; mask=m1 }, Mask { expr=e2; mask=m2 }
      -> eq e1 e2 && eq m1 m2
    | Range { lo=l1; hi=h1 }, Range { lo=l2; hi=h2 }
      -> eq l1 l2 && eq h1 h2
    | _ -> false
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
          typ: Type.t }
      [@@deriving sexp,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,yojson]

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
          name: Types.name;
          args: (Expression.t option) list }
      [@@deriving sexp,yojson]

      type typed_action_ref =
        { action: pre_action_ref;
          typ: Type.t }
      [@@deriving sexp,yojson]

      type action_ref = typed_action_ref info [@@deriving sexp,yojson]

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
        { annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
      [@@deriving sexp,yojson]

      type property = pre_property info [@@deriving sexp,yojson]

      let name_of_property (_, {name; _}) =
        snd name
end

and Statement : sig
      type pre_switch_label =
          Default
        | Name of P4String.t
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
    | Name of P4String.t [@name "name"]
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
          next: P4String.t }
      [@@deriving sexp,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,yojson]

      type pre_transition =
          Direct of
            { next: P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,yojson]

      type transition = pre_transition info [@@deriving sexp,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,yojson]

      type state = pre_state info [@@deriving sexp,yojson]
end = struct
      type pre_case =
        { matches: Match.t list;
          next: P4String.t }
      [@@deriving sexp,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,yojson]

      type pre_transition =
          Direct of
            { next: P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,yojson]

      type transition = pre_transition info [@@deriving sexp,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: P4String.t;
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
        name: P4String.t;
        value: Value.value }
  | Instantiation of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        args: Expression.t list;
        name: P4String.t;
        init: Block.t option; }
  | Parser of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | Variable of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: P4String.t;
        init: Expression.t option }
  | ValueSet of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        size: Expression.t;
        name: P4String.t }
  | Action of
      { annotations: Annotation.t list;
        name: P4String.t;
        data_params: TypeParameter.t list;
        ctrl_params: TypeParameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: P4String.t;
        key: Table.key list;
        actions: Table.action_ref list;
        entries: (Table.entry list) option;
        default_action: Table.action_ref option;
        size: P4Int.t option;
        custom_properties: Table.property list }
  | Header of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | HeaderUnion of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | Struct of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | Error of
      { members: P4String.t list }
  | MatchKind of
      { members: P4String.t list }
  | Enum of
      { annotations: Annotation.t list;
        name: P4String.t;
        members: P4String.t list }
  | SerializableEnum of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: P4String.t;
        members: (P4String.t * Expression.t) list }
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
  | ControlType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
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
        value: Value.value }
  | Instantiation of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        args: Expression.t list;
        name: P4String.t;
        init: Block.t option; }
  | Parser of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        states: Parser.state list }
  | Control of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        constructor_params: TypeParameter.t list;
        locals: t list;
        apply: Block.t }
  | Function of
      { return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list;
        body: Block.t }
  | ExternFunction of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | Variable of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: P4String.t;
        init: Expression.t option }
  | ValueSet of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        size: Expression.t;
        name: P4String.t }
  | Action of
      { annotations: Annotation.t list;
        name: P4String.t;
        data_params: TypeParameter.t list;
        ctrl_params: TypeParameter.t list;
        body: Block.t }
  | Table of
      { annotations: Annotation.t list;
        name: P4String.t;
        key: Table.key list;
        actions: Table.action_ref list;
        entries: (Table.entry list) option;
        default_action: Table.action_ref option;
        size: P4Int.t option;
        custom_properties: Table.property list }
  | Header of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | HeaderUnion of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | Struct of
      { annotations: Annotation.t list;
        name: P4String.t;
        fields: field list }
  | Error of
      { members: P4String.t list }
  | MatchKind of
      { members: P4String.t list }
  | Enum of
      { annotations: Annotation.t list;
        name: P4String.t;
        members: P4String.t list }
  | SerializableEnum of
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: P4String.t;
        members: (P4String.t * Expression.t) list }
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
  | ControlType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | ParserType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
  | PackageType of
      { annotations: Annotation.t list;
        name: P4String.t;
        type_params: P4String.t list;
        params: TypeParameter.t list }
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

  (*type entries = Table.pre_entry list*)
  type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list

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

  val assert_action_decl : Declaration.t -> TypeParameter.t list

end = struct
  type buf = Cstruct_sexp.t [@@deriving sexp]
  let buf_to_yojson b = failwith "unimplemented"
  let buf_of_yojson j = failwith "unimplemented"

  type pkt = {
    emitted : buf;
    main : buf;
    in_size : int;
  } [@@deriving sexp,yojson]

  (*type entries = Table.pre_entry list*)
  type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list

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
      typ: Type.t }
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

  let assert_action_decl (d : Declaration.t) : TypeParameter.t list = 
    match snd d with
    | Action {data_params;ctrl_params;_} -> data_params @ ctrl_params
    | _ -> failwith "not an action declaration"
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


type program =
    Program of Declaration.t list [@name "program"]
