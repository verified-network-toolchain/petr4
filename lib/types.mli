(* Copyright 2019-present Cornell University
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

(** This module defines the Intermediate Represenation (IR) for parsed
   P4 programs. The module first defines a few top-level types and
   helper functions, followed by a a series of modules, one for each
   type of syntactic construct in a P4 program. Generally the
   sub-modules define a type [pre_t] which represents the actual IR as
   well as a type [t], which is just [pre_t] annotated with parsing
   information. *)

open Util

(** ['a info] types represents an IR nodes annotated with parsing information. *)
(* type 'a info = Info.t * 'a [@@deriving sexp,show,yojson] *)

(** [info x] returns the parsing info associated with an IR node [x].*) 
(* val info : 'a info -> Info.t *)

(** [P4Int.t] represents an integer literal, with an optional sign and width *)
module P4Int : sig
  type 'a pt =
    { tags : 'a;
      value: bigint;
      width_signed: (int * bool) option}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

(** [P4String.t] represents a string literal. *)
module P4String : sig
  type 'a pt = 
    { tags:'a; 
      string:string}
  [@@deriving sexp,show,yojson]

   type t = Info.t pt [@@deriving sexp,show,yojson]

   val insert_dummy_tags : string -> t

   val mk_p4string : 'a -> string -> 'a pt
end

(** [name] represents a name, which is either a bare name like [x] or a 
    qualified name like [x.y] *)
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

val name_tags : 'a pname -> 'a

val mk_barename : 'a -> 'a P4String.pt -> 'a pname

val mk_barename_from_string : 'a -> string -> 'a pname

val insert_dummy_tags : P4String.t -> name

val mk_barename_with_dummy : string -> name

val to_bare : name -> name
(* val name_info: name -> Info.t *)
val name_eq : name -> name -> bool
val name_only : name -> string

(** [KeyValue.t] represents a key-value pair; the key is a [P4String.t] 
    and the value is an [Expression.t]  *)
module rec KeyValue : sig
  type 'a pt =
    { tags : 'a;
      key : P4String.t;
      value : Expression.t}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

(** [Annotation.t] represents an annotation, which has a [name] and a [body]. 
    The [body] is either [Empty], an [Unparsed] string, an [Expression] or 
    a [KeyValue]. *)
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
end

(** [Parameter.t] represents a parameter, with an optional list of [annotations], 
    an optional [direction], a [typ], a [variable], and an optional [opt_value]. *)
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
end

(** [Op.t] represents operators, which are either [uni] or [bin], 
    for unary and binary respectively. *)
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

end

(** [Type.t] represents a P4 type. *)
and Type : sig
  (** [Type.t] definition *)
  type 'a pt =
      Bool of {tags: 'a} (** Booleans *)
    | Error of {tags: 'a} (** Error *)
    | Integer of {tags: 'a} (** Infinite-precision integers *)
    | IntType of 
        { tags: 'a; 
          expr: Expression.t}
      (** Fixed-with signed integers *)
    | BitType of 
        { tags: 'a; 
          expr: Expression.t}
      (** Fixed-width unsigned integers *)
    | VarBit of 
        { tags: 'a; 
          expr: Expression.t}
      (** Variable-width integers with a maximum width *)
    | TypeName of 
        { tags: 'a; 
          name: name} 
      (** Named types *)
    | SpecializedType of
        { tags: 'a;
          base: t;
          args: t list} 
      (** Type applications, with a base type and a list of type arguments. *)
    | HeaderStack of
        { tags: 'a;
          header: t;
          size:  Expression.t} 
      (** Header stacks with a header type and a size *)
    | Tuple of 
        { tags: 'a; 
          xs: t list}
      (** Tuples *) 
    | String of {tags: 'a} (** Strings *)
    | Void of {tags: 'a} (** Void *)
    | DontCare of {tags: 'a} (** Don't Care (written [_]) *)
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]
  val eq : t -> t -> bool
  val tags : 'a pt -> 'a
end

(** [MethodPrototype.t] represents a method prototype, which come in three 
    flavors. *)
and MethodPrototype : sig
  type 'a pt =
      Constructor of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list } 
      (** Constructors, with [annotations], a [name], and [parameters]. *) 
    | AbstractMethod of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list} 
      (** Abstract methods, with [annotations], a [return] type, a [name], 
          [type_params], and [params]. *)
    | Method of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list} 
      (** Abstract Methods, which also come, with [annotations], 
          a [return] type, a [name], [type_params], and [params]. *)
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

(** [Argument.t] rsepresents an argument, which comes in three flavors. *)
and Argument : sig
  type 'a pt  =
      Expression of
        { tags: 'a;
          value: Expression.t }
      (** Expressions with a [value]. *)
    | KeyValue of
        { tags: 'a;
          key: P4String.t;
          value: Expression.t }
      (** Key-value pairs with a [key] and a [value]. *)
    | Missing of {tags: 'a}
      (** Missing (written [_]). *)
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]
end

(** [Direction.t] encodes a direction indication for a parameter: [In], [Out], 
    or [InOut]. *)
and Direction : sig
   type 'a pt =
      In of {tags: 'a}
    | Out of {tags: 'a}
    | InOut of {tags: 'a}
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

  val tags : 'a pt -> 'a 
end

(** [Expression.t] represents a P4 expression. *)
and Expression : sig
  type 'a pt =
      True of {tags: 'a} (** Boolean [true] literals *)
    | False of {tags: 'a} (** Boolean [false] literal *) 
    | Int of 
        { tags: 'a;
          x: P4Int.t}
      (** Integer literal *)
    | String of 
        { tags: 'a;
          str: P4String.t}
      (** String literal *)
    | Name of 
        { tags: 'a;
          name: name}
      (** Names *)
    | ArrayAccess of
        { tags: 'a;
          array: t;
          index: t }
      (** Header stack access *)
    | BitStringAccess of
        { tags: 'a;
          bits: t;
          lo: t;
          hi: t }
      (** Bit slice *)
    | List of
        { tags: 'a;
          values: t list }
      (** Lists *)
    | Record of
        { tags: 'a;
          entries: KeyValue.t list }
      (** Structs *)
    | UnaryOp of
        { tags: 'a;
          op: Op.uni;
          arg: t }
      (** Unary operations *) 
    | BinaryOp of
        { tags: 'a;
          op: Op.bin;
          args: (t * t) }
      (** Binary operations *)
    | Cast of
        { tags: 'a;
          typ: Type.t;
          expr: t }
      (** Type casts *)
    | TypeMember of
        { tags: 'a;
          typ: name;
          name: P4String.t }
      (** Type members. *)
    | ErrorMember of 
        {tags: 'a;
         err: P4String.t}
      (** Error members *)
    | ExpressionMember of
        { tags: 'a;
          expr: t;
          name: P4String.t }
      (** Expression members *)
    | Ternary of
        { tags: 'a;
          cond: t;
          tru: t;
          fls: t }
      (** Conditionals *)
    | FunctionCall of
        { tags: 'a;
          func: t;
          type_args: Type.t list;
          args: Argument.t list }
      (** Function calls. *)
    | NamelessInstantiation of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list }
      (** Anonymous instantiation *)
    | Mask of
        { tags: 'a;
          expr: t;
          mask: t }
      (** Bit mask. *)
    | Range of
        { tags: 'a;
          lo: t;
          hi: t }
      (** Ranges *)
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]
      val tags : 'a pt -> 'a
      val update_tags : 'a pt -> 'a -> 'a pt
end

(** [Table.t] represents a table declaration *)
and Table : sig
  (** [action_ref] represents action references, with optional [annotations], 
      a [name], and [args]. *)
  type 'a paction_ref =
    { tags: 'a;
      annotations: Annotation.t list;
      name: name;
      args: Argument.t list }
  [@@deriving sexp,show,yojson]

  type action_ref = Info.t paction_ref [@@deriving sexp,show,yojson]

  (** [key] represents table keys, with optional [annotations], a [key], 
      and a [match_kind]. *)
  type 'a pkey =
    { tags: 'a;
      annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4String.t }
  [@@deriving sexp,show,yojson]

  type key = Info.t pkey [@@deriving sexp,show,yojson]

  (** [entry] represents table entries with optional [annotations], [matches], 
      and an [action]. *)
  type 'a pentry =
    { tags: 'a;
      annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,show,yojson { exn = true }]

  type entry = Info.t pentry [@@deriving sexp,show,yojson]

  (** [property] represents a table property, which come in four flavors. *)
  type 'a pproperty =
      Key of
        { tags: 'a;
          keys: key list }
      (** Keys *)
    | Actions of
        { tags: 'a;
          actions: action_ref list }
      (** Actions *)
    | Entries of
        { tags: 'a;
          entries: entry list }
      (** Entries *)
    | Custom of
        { tags: 'a;
          annotations: Annotation.t list;
          const: bool;
          name: P4String.t;
          value: Expression.t }
      (** Custom (e.g., [size], [default_action], etc.) *)
  [@@deriving sexp,show,yojson]

  type property = Info.t pproperty [@@deriving sexp,show,yojson]

  val name_of_property : property -> string

end

(** [Match.t] represents pattern matches for [select] statements. *)
and Match : sig
  type 'a pt =
      Default of {tags: 'a}
      (** Default (written [default]). *)
    | DontCare of {tags: 'a}
      (** Don't care (written [_] and equivalent to [default]. *)
    | Expression of
        { tags: 'a;
          expr: Expression.t }
      (** Expression with an [expr]. *)
  [@@deriving sexp,show,yojson { exn = true }]

  type t = Info.t pt [@@deriving sexp,show,yojson { exn = true }]

  val tags : 'a pt -> 'a
  
end

(** [Parser.t] represents parser declarations *)
and Parser : sig

  (** [case] represents a [select] [case] with [matches] and [next] state. *) 
  type 'a pcase =
    { tags: 'a; 
      matches: Match.t list;
      next: P4String.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type case = Info.t pcase [@@deriving sexp,show,yojson]
  
  (** [transition] represents a transition statement, which is either [Direct],
      with a [next], or a [Select] with [exprs] and [cases]. *)
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

  (** [state] represents a state with optional [annotations], a [name], 
      [statements], and a [transition]. *)
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
end

(** [Declaration.t] represents a top-level declaration *)
and Declaration : sig
  type 'a pt =
      Constant of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
      (** Constants *)
    | Instantiation of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
      (** Instantiation *)
    | Parser of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
      (** Parsers *)
    | Control of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
      (** Controls *)
    | Function of
        { tags: 'a;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
      (** Functions *)
    | ExternFunction of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
      (** Extern functions *) 
    | Variable of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
      (** Variables *) 
    | ValueSet of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          size: Expression.t;
          name: P4String.t }
      (** Parser value sets *)
    | Action of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
      (** Actions *)
    | Table of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
      (** Tables *)
    | Header of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
      (** Header types *)
    | HeaderUnion of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
      (** Header union types *)
    | Struct of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
      (** Struct types *)
    | Error of
        { tags: 'a;
          members: P4String.t list }
      (** Error types *)
    | MatchKind of
        { tags: 'a;
          members: P4String.t list }
      (** Match kind types *)
    | Enum of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          members: P4String.t list }
      (** Enumerated types *)
    | SerializableEnum of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          members: (P4String.t * Expression.t) list }
      (** Serializable enumerated types *)
    | ExternObject of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
      (** Extern objects *)
    | TypeDef of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
      (** Type definitions *)
    | NewType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
      (** Generative type definitions *)
    | ControlType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
      (** Control types *) 
    | ParserType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
      (** Parser types *)
    | PackageType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
      (** Package types *)
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  (** [field] represents a field of a [struct], [header], etc. 
      with [annotations], a [typ], and a [name]. *)
  and 'a pfield =
    { tags: 'a;
      annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,show,yojson]

  and field = Info.t pfield [@@deriving sexp,show,yojson]

  val name : t -> P4String.t

  val tags : 'a pt -> 'a

  val name_opt : t -> P4String.t option

end

(** [Statement.t] represents a P4 statement *)
and Statement : sig
  
  (** [switch_label] represents the label on a switch statement, which is 
      either [default] or a [name] *)
  type 'a pswitch_label =
      Default of {tags: 'a}
    | Name of 
        { tags: 'a;
          name: P4String.t}
  [@@deriving sexp,show,yojson]

  type switch_label = Info.t pswitch_label [@@deriving sexp,show,yojson]

  val tags_label : 'a pswitch_label -> 'a

  (** [switch case] represents a case of a switch statement, which is either 
      an [Action] with a [label]ed block of [code], or a [FallThrough] 
      with just a [label]. *)
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

  (** [Statement.t] comes in 10 flavors. *) 
  type 'a pt =
      MethodCall of
        { tags: 'a;
          func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list }
      (** Method call *)
    | Assignment of
        { tags: 'a;
          lhs: Expression.t;
          rhs: Expression.t }
      (** Assignment *)
    | DirectApplication of
        { tags: 'a;
          typ: Type.t [@key "type"];
          args: Argument.t list }
      (** Direct application *)
    | Conditional of
        { tags: 'a;
          cond: Expression.t;
          tru: t;
          fls: t option }
      (** If-Then-Else *)
    | BlockStatement of
        { tags: 'a;
          block: Block.t }
      (** Block statement *)
    | Exit of {tags: 'a} (** Exit *)
    | EmptyStatement of {tags: 'a} (** Empty (written [;]) *)
    | Return of
        { tags: 'a;
          expr: Expression.t option }
      (** Return *)
    | Switch of
        { tags: 'a;
          expr: Expression.t;
          cases: switch_case list }
      (** Switch *)
    | DeclarationStatement of
        { tags: 'a;
          decl: Declaration.t }
      (** Declaration *)
  [@@deriving sexp,show,yojson]

  and t = Info.t pt [@@deriving sexp,show,yojson]

  val tags : 'a pt -> 'a

end

(** [Block.t] represents a block of statements, with [annotations] and a list of [statements]. *) 
and Block : sig
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,show,yojson]

  type t = Info.t pt [@@deriving sexp,show,yojson]

end

(** [program] represents a P4 program with a [Declaration.t] list. *)
type program =
  Program of Declaration.t list [@@deriving sexp,show,yojson]
