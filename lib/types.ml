(* Copyright 2018-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
*)

open Util

open Sexplib.Conv

(* reminder: you're missing info, info_to_yojson, and info_of_yojson!!! *)

(* this doesn't work. error: unbound record field info.
  let info_to_yojson f x = f (x.info) 
 *)

(* let info_of_yojson f json =
  match f json with
  | Ok pre -> Ok (Info.M "<yojson>", pre)
  | Error x -> Error x
 *)

module P4Int = struct

  type 'a pt =
    { tags : 'a;
      value: bigint;
      width_signed: (int * bool) option}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

end

module P4String = struct
  type 'a pt = 
    { tags:'a; 
      string:string}
  [@@deriving sexp,show,yojson]

   type t = Info.t pt [@@deriving sexp,show,yojson]

   (* Constructs a p4string from a string by inserting info.dummy for tags. *)
   let insert_dummy_tags : string -> t =
     function s -> {tags = Info.dummy; string = s}

   (* Constructs a p4string from a tags and a string. *)
   let mk_p4string : 'a -> string -> 'a pt =
     fun t s -> {tags = t; string = s}
end

type 'a pname =
  | BareName of 
      { tags:'a; 
        name: 'a P4String.pt}
  | QualifiedName of 
      { tags:'a; 
        prefix: 'a P4String.pt list; 
        name: 'a P4String.pt}
[@@deriving sexp,show,yojson]

type name = Info.t pname [@@deriving sexp,show,yojson]

(* returns the tags of a name. *)
let name_tags (name : 'a pname) : 'a =
  match name with
  | BareName {tags; _}
  | QualifiedName {tags; _}
      -> tags

(* Constructs a barename from a p4string and a tags. *)
let mk_barename : 'a -> 'a P4String.pt -> 'a pname =
  fun t n -> BareName {tags = t; name = n}

(* Constructs a barename from a string and a tags. *)
let mk_barename_from_string : 'a -> string -> 'a pname =
  fun t s -> mk_barename t (P4String.mk_p4string t s)

(* Constructs a Barename from a p4String by adding a dummy tag. *)
let insert_dummy_tags : P4String.t -> name =
  function n -> mk_barename Info.dummy n

(* Constructs a Barename from a string by inserting info.dummy for tags. *)
let mk_barename_with_dummy : string -> name =
  fun s -> mk_barename_from_string Info.dummy s

let to_bare : name -> name = function
  | QualifiedName n -> BareName {tags = n.tags; name = n.name}
  | n -> n


let name_eq n1 n2 =
  match n1, n2 with
  | BareName s1,
    BareName s2 ->
    s1.name = s2.name
  | QualifiedName {tags = _; prefix = ns1; name = s1},
    QualifiedName {tags = _; prefix = ns2; name = s2} ->
    s1 = s2 && ns1 = ns2
  | _ -> false
  (* DISCUSS: how do prefixes agree? list =? or the order and repetition doesn't matter? *)

and name_only n =
  match n with
  | BareName s -> s.name.string
  | QualifiedName s -> s.name.string

module rec KeyValue : sig
  type 'a pt =
    { tags : 'a;
      key : P4String.t;
      value : Expression.t}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end = struct
  type 'a pt =
    { tags : 'a;
      key : P4String.t;
      value : Expression.t }
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end
and Annotation : sig
  type 'a pbody =
    | Empty of 
        { tags: 'a}
    | Unparsed of 
        { tags: 'a; 
          str: P4String.t list}
    | Expression of 
        { tags: 'a; 
          exprs: Expression.t list}
    | KeyValue of 
        { tags: 'a; 
          k_v: KeyValue.t list} 
  [@@deriving sexp,show,yojson]

  type body = Info.t pbody [@@deriving sexp,show,yojson]

  type 'a pt =
    { tags: 'a;
      name: P4String.t;
      body: body}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

end = struct
  type 'a pbody =
    | Empty of 
        { tags: 'a}
    | Unparsed of 
        { tags: 'a; 
          str: P4String.t list}
    | Expression of 
        { tags: 'a; 
          exprs: Expression.t list}
    | KeyValue of 
        { tags: 'a; 
          k_v: KeyValue.t list} 
  [@@deriving sexp,show,yojson]

  type body = Info.t pbody [@@deriving sexp,show,yojson]

  type 'a pt =
    { tags: 'a;
      name: P4String.t;
      body: body}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

end

and Parameter : sig
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end = struct
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4String.t;
      opt_value: Expression.t option}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

and Op : sig
  type 'a puni =
      Not of {tags: 'a}
    | BitNot of {tags: 'a}
    | UMinus of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type uni = Info.t puni [@@deriving sexp,show,yojson]

  val eq_uni : uni -> uni -> bool
  val tags_uni : 'a puni -> 'a
  
  type 'a pbin =
      Plus of {tags: 'a}
    | PlusSat of {tags: 'a}
    | Minus of {tags: 'a}
    | MinusSat of {tags: 'a}
    | Mul of {tags: 'a}
    | Div of {tags: 'a}
    | Mod of {tags: 'a}
    | Shl of {tags: 'a}
    | Shr of {tags: 'a}
    | Le of {tags: 'a}
    | Ge of {tags: 'a}
    | Lt of {tags: 'a}
    | Gt of {tags: 'a}
    | Eq of {tags: 'a}
    | NotEq of {tags: 'a}
    | BitAnd of {tags: 'a}
    | BitXor of {tags: 'a}
    | BitOr of {tags: 'a}
    | PlusPlus of {tags: 'a}
    | And of {tags: 'a}
    | Or of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type bin = Info.t pbin [@@deriving sexp,show,yojson]

  val eq_bin : bin -> bin -> bool
  val tags_bin : 'a pbin -> 'a

end = struct
  type 'a puni =
      Not of {tags: 'a}
    | BitNot of {tags: 'a}
    | UMinus of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type uni = Info.t puni [@@deriving sexp,show,yojson]

  let eq_uni u1 u2 =
    match u1,u2 with
    | Not _, Not _
    | BitNot _, BitNot _
    | UMinus _, UMinus _ -> true
    | _ -> false

  let tags_uni u =
    match u with
    | Not {tags}
    | BitNot {tags}
    | UMinus {tags}
      -> tags

  type 'a pbin =
      Plus of {tags: 'a}
    | PlusSat of {tags: 'a}
    | Minus of {tags: 'a}
    | MinusSat of {tags: 'a}
    | Mul of {tags: 'a}
    | Div of {tags: 'a}
    | Mod of {tags: 'a}
    | Shl of {tags: 'a}
    | Shr of {tags: 'a}
    | Le of {tags: 'a}
    | Ge of {tags: 'a}
    | Lt of {tags: 'a}
    | Gt of {tags: 'a}
    | Eq of {tags: 'a}
    | NotEq of {tags: 'a}
    | BitAnd of {tags: 'a}
    | BitXor of {tags: 'a}
    | BitOr of {tags: 'a}
    | PlusPlus of {tags: 'a}
    | And of {tags: 'a}
    | Or of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type bin = Info.t pbin [@@deriving sexp,show,yojson]

  let eq_bin b1 b2 =
    match b1,b2 with
    | Plus _, Plus _
    | PlusSat _, PlusSat _
    | Minus _, Minus _
    | MinusSat _, MinusSat _
    | Mul _, Mul _
    | Div _, Div _
    | Mod _, Mod _ 
    | Shl _, Shl _ 
    | Shr _, Shr _
    | Le _, Le _ 
    | Ge _, Ge _ 
    | Lt _, Lt _ 
    | Gt _, Gt _ 
    | Eq _, Eq _
    | NotEq _, NotEq _
    | BitAnd _, BitAnd _
    | BitXor _, BitXor _
    | BitOr _, BitOr _
    | PlusPlus _, PlusPlus _
    | And _, And _
    | Or _, Or _ -> true
    | _ -> false

  let tags_bin bin =
    match bin with
    | Plus {tags}
    | PlusSat {tags}
    | Minus {tags}
    | MinusSat {tags}
    | Mul {tags}
    | Div {tags}
    | Mod {tags}
    | Shl {tags}
    | Shr {tags}
    | Le {tags}
    | Ge {tags}
    | Lt {tags}
    | Gt {tags}
    | Eq {tags}
    | NotEq {tags}
    | BitAnd {tags}
    | BitXor{tags}
    | BitOr {tags}
    | PlusPlus {tags}
    | And {tags}
    | Or {tags}
      -> tags
end

and Type : sig
  type 'a pt =
      Bool of {tags: 'a}
    | Error of {tags: 'a}
    | Integer of {tags: 'a}
    | IntType of 
        { tags: 'a; 
          expr: Expression.t}
    | BitType of 
        { tags: 'a; 
          expr: Expression.t}
    | VarBit of 
        { tags: 'a; 
          expr: Expression.t}
    (* this could be a typename or a type variable. *)
    | TypeName of 
        { tags: 'a; 
          name: name}
    | SpecializedType of
        { tags: 'a;
          base: t;
          args: t list}
    | HeaderStack of
        { tags: 'a;
          header: t;
          size:  Expression.t}
    | Tuple of 
        { tags: 'a; 
          xs: t list}
    | String of {tags: 'a}
    | Void of {tags: 'a}
    | DontCare of {tags: 'a}
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]
  val eq : t -> t -> bool
  val tags : 'a pt -> 'a
end = struct
  type 'a pt =
      Bool of {tags: 'a} [@name "bool"]
    | Error of {tags: 'a} [@name "error"]
    | Integer of {tags: 'a} [@name "integer"]
    | IntType of 
        { tags: 'a;
          expr: Expression.t} [@name "int"]
    | BitType of 
        { tags: 'a;
          expr: Expression.t} [@name "bit"]
    | VarBit of 
        { tags: 'a;
          expr: Expression.t} [@name "varbit"]
    | TypeName of 
        { tags: 'a;
          name: name} [@name "name"]
    | SpecializedType of
        { tags: 'a;
          base: t;
          args: t list } [@name "specialized"]
    | HeaderStack of
        { tags: 'a;
          header: t;
          size:  Expression.t } [@name "header_stack"]
    | Tuple of 
        { tags: 'a;
          xs: t list} [@name "tuple"]
    | String of {tags: 'a} [@name "string"]
    | Void of {tags: 'a} [@name "void"]
    | DontCare of {tags: 'a} [@name "dont_care"]
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  let rec eq t1 t2 = 
    match t1, t2 with
    | Bool _, Bool _
    | Error _, Error _
    | Integer _, Integer _
    | String _, String _
    | Void _, Void _
    | DontCare _, DontCare _ -> true
    | IntType e1, IntType e2 -> failwith "TODO"
    | BitType e1, BitType e2 -> failwith "TODO"
    | VarBit e1, VarBit e2 -> failwith "TODO"
    | TypeName n1, TypeName n2 ->
      name_eq n1.name n2.name
    | SpecializedType { tags=_; base=b1; args=a1 },
      SpecializedType { tags=_; base=b2; args=a2 }
      -> eq b1 b2 &&
         begin match Base.List.for_all2 a1 a2 ~f:eq with
           | Ok tf -> tf
           | Unequal_lengths -> false
         end
    | HeaderStack { tags=_; header=h1; size=s1 },
      HeaderStack { tags=_; header=h2; size=s2 }
      -> eq h1 h2 && failwith "TODO"
    | Tuple t1, Tuple t2 ->
      begin match Base.List.for_all2 t1.xs t2.xs ~f:eq with
        | Ok tf -> tf
        | Unequal_lengths -> false
      end
    | _ -> false

  let tags (t: 'a pt) : 'a =
    match t with
    | Bool {tags}
    | Error {tags}
    | Integer {tags}
    | IntType {tags; _}
    | BitType {tags; _}
    | VarBit {tags; _}
    | TypeName {tags; _}
    | SpecializedType {tags; _}
    | HeaderStack {tags; _}
    | Tuple {tags; _}
    | String {tags}
    | Void {tags}
    | DontCare {tags}
        -> tags
end

and MethodPrototype : sig
  type 'a pt =
      Constructor of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list }
    | AbstractMethod of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
    | Method of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end = struct
  type 'a pt =
      Constructor of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list }
    | AbstractMethod of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
    | Method of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

and Argument : sig
  type 'a pt  =
      Expression of
        { tags: 'a;
          value: Expression.t }
    | KeyValue of
        { tags: 'a;
          key: P4String.t;
          value: Expression.t }
    | Missing of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end = struct
  type 'a pt  =
      Expression of
        { tags: 'a;
          value: Expression.t }
    | KeyValue of
        { tags: 'a;
          key: P4String.t;
          value: Expression.t }
    | Missing of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

and Direction : sig
  type 'a pt =
      In of {tags: 'a}
    | Out of {tags: 'a}
    | InOut of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

  val tags : 'a pt -> 'a
end = struct
  type 'a pt =
      In of {tags: 'a}
    | Out of {tags: 'a}
    | InOut of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

  let tags dir : 'a =
    match dir with
    | In {tags}
    | Out {tags}
    | InOut {tags}
        -> tags
end

and Expression : sig
  type 'a pt =
      True of {tags: 'a}
    | False of {tags: 'a}
    | Int of 
        { tags: 'a;
          x: P4Int.t}
    | String of 
        { tags: 'a;
          str: P4String.t}
    | Name of 
        { tags: 'a;
          name: name}
    | ArrayAccess of
        { tags: 'a;
          array: t;
          index: t }
    | BitStringAccess of
        { tags: 'a;
          bits: t;
          lo: t;
          hi: t }
    | List of
        { tags: 'a;
          values: t list }
    | Record of
        { tags: 'a;
          entries: KeyValue.t list }
    | UnaryOp of
        { tags: 'a;
          op: Op.uni;
          arg: t }
    | BinaryOp of
        { tags: 'a;
          op: Op.bin;
          args: (t * t) }
    | Cast of
        { tags: 'a;
          typ: Type.t;
          expr: t }
    | TypeMember of
        { tags: 'a;
          typ: name;
          name: P4String.t }
    | ErrorMember of 
        {tags: 'a;
         err: P4String.t}
    | ExpressionMember of
        { tags: 'a;
          expr: t;
          name: P4String.t }
    | Ternary of
        { tags: 'a;
          cond: t;
          tru: t;
          fls: t }
    | FunctionCall of
        { tags: 'a;
          func: t;
          type_args: Type.t list;
          args: Argument.t list }
    | NamelessInstantiation of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list }
    | Mask of
        { tags: 'a;
          expr: t;
          mask: t }
    | Range of
        { tags: 'a;
          lo: t;
          hi: t }
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

      val tags : 'a pt -> 'a

      val update_tags : 'a pt -> 'a -> 'a pt

end = struct
  type 'a pt =
      True of {tags: 'a} [@name "true"]
    | False of {tags: 'a} [@name "false"]
    | Int of 
        { tags: 'a;
          x: P4Int.t} [@name "int"]
    | String of 
        { tags: 'a;
          str: P4String.t} [@name "string"]
    | Name of 
        { tags: 'a;
          name: name} [@name "name"]
    | ArrayAccess of
        { tags: 'a;
          array: t;
          index: t } [@name "array_access"]
    | BitStringAccess of
        { tags: 'a;
          bits: t;
          lo: t;
          hi: t } [@name "bit_string_access"]
    | List of
        { tags: 'a;
          values: t list } [@name "list"]
    | Record of
        { tags: 'a;
          entries: KeyValue.t list } [@name "struct"]
    | UnaryOp of
        { tags: 'a;
          op: Op.uni;
          arg: t } [@name "unary_op"]
    | BinaryOp of
        { tags: 'a;
          op: Op.bin;
          args: (t * t) } [@name "binary_op"]
    | Cast of
        { tags: 'a;
          typ: Type.t [@key "type"];
          expr: t }  [@name "cast"]
    | TypeMember of
        { tags: 'a;
          typ: name [@key "type"];
          name: P4String.t } [@name "type_member"]
    | ErrorMember of 
        { tags: 'a;
          err: P4String.t} [@name "error_member"]
    | ExpressionMember of
        { tags: 'a;
          expr: t;
          name: P4String.t } [@name "expression_member"]
    | Ternary of
        { tags: 'a;
          cond: t;
          tru: t;
          fls: t } [@name "ternary"]
    | FunctionCall of
        { tags: 'a;
          func: t;
          type_args: Type.t list;
          args: Argument.t list } [@name "call"]
    | NamelessInstantiation of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list } [@name "instantiation"]
    | Mask of
        { tags: 'a;
          expr: t;
          mask: t } [@name "mask"]
    | Range of
        { tags: 'a;
          lo: t;
          hi: t } [@name "range"]
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

      let tags (exp: 'a pt) : 'a =
        match exp with
        | True {tags}
        | False {tags}
        | Int {tags; _}
        | String {tags; _}
        | Name {tags; _}
        | ArrayAccess {tags; _}
        | BitStringAccess {tags; _}
        | List {tags; _}
        | Record {tags; _}
        | UnaryOp {tags; _}
        | BinaryOp {tags; _}
        | Cast {tags; _}
        | TypeMember {tags; _}
        | ErrorMember {tags; _}
        | ExpressionMember {tags; _}
        | Ternary {tags; _}
        | FunctionCall {tags; _}
        | NamelessInstantiation {tags; _}
        | Mask {tags; _}
        | Range {tags; _} -> tags

      let update_tags (exp : 'a pt) (tags : 'a) : 'a pt =
        match exp with
        | True {tags = _}
          -> True {tags}
        | False {tags = _}
          -> False {tags}
        | Int {x; _}
          -> Int {x; tags}
        | String {str; _}
          -> String {str; tags}
        | Name {name; _}
          -> Name {name; tags}
        | ArrayAccess {array; index; _}
          -> ArrayAccess {array; index; tags}
        | BitStringAccess {bits; lo; hi; _}
          -> BitStringAccess {bits; lo; hi; tags}
        | List {values; _}
            -> List {values; tags}
        | Record {entries; _}
            -> Record {entries; tags}
        | UnaryOp {op; arg; _}
            -> UnaryOp {op; arg; tags}
        | BinaryOp {op; args; _}
            -> BinaryOp {op; args; tags}
        | Cast {typ; expr; _}
            -> Cast {typ; expr; tags}
        | TypeMember {typ; name; _}
            -> TypeMember {typ; name; tags}
        | ErrorMember {err; _}
            -> ErrorMember {err; tags}
        | ExpressionMember {expr; name; _}
            -> ExpressionMember {expr; name; tags}
        | Ternary {cond; tru; fls; _}
            -> Ternary {cond; tru; fls; tags}
        | FunctionCall {func; type_args; args; _}
            -> FunctionCall {func; type_args; args; tags}
        | NamelessInstantiation {typ; args; _}
            -> NamelessInstantiation {typ; args; tags}
        | Mask {expr; mask; _}
            -> Mask {expr; mask; tags}
        | Range {lo; hi; _}
            -> Range {lo; hi; tags}

end

and Table : sig
  type 'a paction_ref =
    { tags: 'a;
      annotations: Annotation.t list;
      name: name;
      args: Argument.t list }
  [@@deriving sexp,show,yojson]

  type action_ref = Info.t paction_ref [@@deriving sexp,show,yojson]

  type 'a pkey =
    { tags: 'a;
      annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4String.t }
  [@@deriving sexp,show,yojson]

  type key = Info.t pkey [@@deriving sexp,show,yojson]

  type 'a pentry =
    { tags: 'a;
      annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,show,yojson { exn = true }]

  type entry = Info.t pentry [@@deriving sexp,show,yojson]

  type 'a pproperty =
      Key of
        { tags: 'a;
          keys: key list }
    | Actions of
        { tags: 'a;
          actions: action_ref list }
    | Entries of
        { tags: 'a;
          entries: entry list }
    | Custom of
        { tags: 'a;
          annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
  [@@deriving sexp,show,yojson]

  type property = Info.t pproperty [@@deriving sexp,show,yojson]

  val name_of_property : property -> string
end = struct
  type 'a paction_ref =
    { tags: 'a;
      annotations: Annotation.t list;
      name: name;
      args: Argument.t list }
  [@@deriving sexp,show,yojson]

  type action_ref = Info.t paction_ref [@@deriving sexp,show,yojson]

  type 'a pkey =
    { tags: 'a;
      annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4String.t }
  [@@deriving sexp,show,yojson]

  type key = Info.t pkey [@@deriving sexp,show,yojson]

  type 'a pentry =
    { tags: 'a;
      annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,show,yojson { exn = true }]

  type entry = Info.t pentry [@@deriving sexp,show,yojson]

  type 'a pproperty =
      Key of
        { tags: 'a;
          keys: key list }
    | Actions of
        { tags: 'a;
          actions: action_ref list }
    | Entries of
        { tags: 'a;
          entries: entry list }
    | Custom of
        { tags: 'a;
          annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
  [@@deriving sexp,show,yojson]

  type property = Info.t pproperty [@@deriving sexp,show,yojson]

  let name_of_property  p =
    match p with
    | Key _ -> "key"
    | Actions _ -> "actions"
    | Entries _ -> "entries"
    | Custom {name; _} -> name.string
end

and Match : sig
  type 'a pt =
      Default of {tags: 'a}
    | DontCare of {tags: 'a}
    | Expression of
        { tags: 'a;
          expr: Expression.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type t = Info.t pt [@@deriving sexp,show,yojson { exn = true }]

  val tags : 'a pt -> 'a

end = struct
  type 'a pt =
      Default of {tags: 'a}
    | DontCare of {tags: 'a}
    | Expression of
        { tags: 'a;
          expr: Expression.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type t = Info.t pt [@@deriving sexp,show,yojson { exn = true }]

  let tags m =
    match m with
    | Default {tags}
    | DontCare {tags}
    | Expression {tags; _}
        -> tags
end

and Parser : sig
  type 'a pcase =
    { tags: 'a; 
      matches: Match.t list;
      next: P4String.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type case = Info.t pcase [@@deriving sexp,show,yojson]

  type 'a ptransition =
      Direct of
        { tags: 'a;
          next: P4String.t }
    | Select of
        { tags: 'a;
          exprs: Expression.t list;
          cases: case list }
  [@@deriving sexp,show,yojson]

  type transition = Info.t ptransition [@@deriving sexp,show,yojson]

  type 'a pstate =
    { tags: 'a;
      annotations: Annotation.t list;
      name: P4String.t;
      statements: Statement.t list;
      transition: transition }
  [@@deriving sexp,show,yojson]

  type state = Info.t pstate [@@deriving sexp,show,yojson]

  val transition_tags : 'a ptransition -> 'a

  val update_transition_tags : 'a ptransition -> 'a -> 'a ptransition
end = struct
  type 'a pcase =
    { tags: 'a;
      matches: Match.t list;
      next: P4String.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type case = Info.t pcase [@@deriving sexp,show,yojson]

  type 'a ptransition =
      Direct of
        { tags: 'a;
          next: P4String.t }
    | Select of
        { tags: 'a;
          exprs: Expression.t list;
          cases: case list }
  [@@deriving sexp,show,yojson]

  type transition = Info.t ptransition [@@deriving sexp,show,yojson]

  type 'a pstate =
    { tags: 'a;
      annotations: Annotation.t list;
      name: P4String.t;
      statements: Statement.t list;
      transition: transition }
  [@@deriving sexp,show,yojson]

  type state = Info.t pstate [@@deriving sexp,show,yojson]

  let transition_tags t =
    match t with
    | Direct {tags; _}
    | Select {tags; _}
        -> tags

  let update_transition_tags trans tags =
    match trans with
    | Direct {next; _} -> Direct {tags = tags; next}
    | Select {exprs; cases; _} -> Select {exprs; cases; tags = tags}
end

and Declaration : sig
  type 'a pt =
      Constant of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
    | Instantiation of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
    | Parser of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
    | Control of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
    | Function of
        { tags: 'a;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | Variable of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
    | ValueSet of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          size: Expression.t;
          name: P4String.t }
    | Action of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
    | Header of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | HeaderUnion of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Struct of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Error of
        { tags: 'a;
          members: P4String.t list }
    | MatchKind of
        { tags: 'a;
          members: P4String.t list }
    | Enum of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          members: P4String.t list }
    | SerializableEnum of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          members: (P4String.t * Expression.t) list }
    | ExternObject of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | ControlType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | ParserType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | PackageType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  and 'a pfield =
    { tags: 'a;
      annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,show,yojson]

  and field = Info.t pfield [@@deriving sexp,show,yojson]

  val name : t -> P4String.t

  val tags : 'a pt -> 'a

  val name_opt : t -> P4String.t option

end = struct
  type 'a pt =
      Constant of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
    | Instantiation of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
    | Parser of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
    | Control of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
        [@name "control"]
    | Function of
        { tags: 'a;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | Variable of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
    | ValueSet of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          size: Expression.t;
          name: P4String.t }
    | Action of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
    | Header of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | HeaderUnion of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Struct of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Error of
        { tags: 'a;
          members: P4String.t list }
    | MatchKind of
        { tags: 'a;
          members: P4String.t list }
    | Enum of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          members: P4String.t list }
    | SerializableEnum of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          members: (P4String.t * Expression.t) list }
    | ExternObject of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | ControlType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | ParserType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | PackageType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  and 'a pfield =
    { tags: 'a; 
      annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,show,yojson]

  and field = Info.t pfield [@@deriving sexp,show,yojson]


  let tags decl =
    match decl with
    | Constant {tags; _}
    | Instantiation {tags; _}
    | Parser {tags; _}
    | Control {tags; _}
    | Function {tags; _}
    | ExternFunction {tags; _}
    | Variable {tags; _}
    | ValueSet {tags; _}
    | Action {tags; _}
    | Table {tags; _}
    | Header {tags; _}
    | HeaderUnion {tags; _}
    | Struct {tags; _}
    | Enum {tags; _}
    | SerializableEnum {tags; _}
    | ExternObject {tags; _}
    | TypeDef {tags; _}
    | NewType {tags; _}
    | ControlType {tags; _}
    | ParserType {tags; _}
    | PackageType {tags; _} 
    | Error {tags; _}
    | MatchKind {tags; _}
      -> tags

  let name_opt d =
    match d with
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

and Statement : sig
  type 'a pswitch_label =
      Default of {tags: 'a}
    | Name of 
        { tags: 'a;
          name: P4String.t}
  [@@deriving sexp,show,yojson]

  type switch_label = Info.t pswitch_label [@@deriving sexp,show,yojson]

  val tags_label : 'a pswitch_label -> 'a 

  type 'a pswitch_case =
      Action of
        { tags: 'a;
          label: switch_label;
          code: Block.t }
    | FallThrough of
        { tags: 'a;
          label: switch_label }
  [@@deriving sexp,show,yojson]

  type switch_case = Info.t pswitch_case [@@deriving sexp,show,yojson]

  type 'a pt =
      MethodCall of
        { tags: 'a;
          func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list }
    | Assignment of
        { tags: 'a;
          lhs: Expression.t;
          rhs: Expression.t }
    | DirectApplication of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list }
    | Conditional of
        { tags: 'a;
          cond: Expression.t;
          tru: t;
          fls: t option }
    | BlockStatement of
        { tags: 'a;
          block: Block.t }
    | Exit of {tags: 'a}
    | EmptyStatement of {tags: 'a}
    | Return of
        { tags: 'a;
          expr: Expression.t option }
    | Switch of
        { tags: 'a;
          expr: Expression.t;
          cases: switch_case list }
    | DeclarationStatement of
        { tags: 'a;
          decl: Declaration.t }
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  val tags : 'a pt -> 'a
end = struct
  type 'a pswitch_label =
      Default of {tags: 'a} [@name "default"]
    | Name of 
        { tags: 'a;
          name: P4String.t} [@name "name"]
  [@@deriving sexp,show,yojson]

  type switch_label = Info.t pswitch_label [@@deriving sexp,show,yojson]

  let tags_label lbl =
    match lbl with
    | Default {tags}
    | Name {tags; _}
       -> tags

  type 'a pswitch_case =
      Action of
        { tags: 'a;
          label: switch_label;
          code: Block.t }
    | FallThrough of
        { tags: 'a;
          label: switch_label }
  [@@deriving sexp,show,yojson]

  type switch_case = Info.t pswitch_case [@@deriving sexp,show,yojson]

  type 'a pt =
      MethodCall of
        { tags: 'a;
          func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list } [@name "method_call"]
    | Assignment of
        { tags: 'a;
          lhs: Expression.t;
          rhs: Expression.t } [@name "assignment"]
    | DirectApplication of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list } [@name "direct_application"]
    | Conditional of
        { tags: 'a;
          cond: Expression.t;
          tru: t;
          fls: t option } [@name "conditional"]
    | BlockStatement of
        { tags: 'a;
          block: Block.t } [@name "block"]
    | Exit of {tags: 'a} [@name "exit"]
    | EmptyStatement of {tags: 'a} [@name "empty_statement"]
    | Return of
        { tags: 'a;
          expr: Expression.t option } [@name "return"]
    | Switch of
        { tags: 'a;
          expr: Expression.t;
          cases: switch_case list } [@name "switch"]
    | DeclarationStatement of
        { tags: 'a;
          decl: Declaration.t } [@name "declaration"]
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  let tags (stmt : 'a pt) : 'a =
    match stmt with
    | MethodCall {tags; _}
    | Assignment {tags; _}
    | DirectApplication {tags; _}
    | Conditional {tags; _}
    | BlockStatement {tags; _}
    | Exit {tags}
    | EmptyStatement {tags}
    | Return {tags; _}
    | Switch {tags; _}
    | DeclarationStatement {tags; _}
        -> tags
end

and Block : sig
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end = struct
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

type program =
    Program of Declaration.t list [@name "program"]
[@@deriving sexp,show,yojson]
