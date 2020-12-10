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
type 'a info = Info.t * 'a [@@deriving sexp,show,yojson]

(** [info x] returns the parsing info associated with an IR node [x].*) 
val info : 'a info -> Info.t

(** [KeyValue.t] represents a key-value pair; the key is a [P4string.t] and the value is an [Expression.t]  *)
module rec KeyValue : sig
  type pre_t =
    { key : P4string.t;
      value : Expression.t }
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Annotation.t] represents an annotation, which has a [name] and a [body]. 
   The [body] is either [Empty], an [Unparsed] string, an [Expression] or a [KeyValue]. *)
and Annotation : sig
  type pre_body =
    | Empty
    | Unparsed of P4string.t list
    | Expression of Expression.t list
    | KeyValue of KeyValue.t list
  [@@deriving sexp,show,yojson]

  type body = pre_body info [@@deriving sexp,show,yojson]

  type pre_t =
    { name: P4string.t;
      body: body }
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Parameter.t] represents a parameter, with an optional list of [annotations], 
    an optional [direction], a [typ], a [variable], and an optional [opt_value]. *)
and Parameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4string.t;
      opt_value: Expression.t option}
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Op.t] represents operators, which are either [uni] or [bin], for unary and binary respectively. *)
and Op : sig
  type pre_uni =
      Not
    | BitNot
    | UMinus
  [@@deriving sexp,show,yojson]

  type uni = pre_uni info [@@deriving sexp,show,yojson]

  val eq_uni : uni -> uni -> bool

  type pre_bin =
      Plus
    | PlusSat
    | Minus
    | MinusSat
    | Mul
    | Div
    | Mod
    | Shl
    | Shr
    | Le
    | Ge
    | Lt
    | Gt
    | Eq
    | NotEq
    | BitAnd
    | BitXor
    | BitOr
    | PlusPlus
    | And
    | Or
  [@@deriving sexp,show,yojson]

  type bin = pre_bin info [@@deriving sexp,show,yojson]

  val eq_bin : bin -> bin -> bool
end

(** [Type.t] represents a P4 type. *)
and Type : sig
  (** [Type.t] definition *)
  type pre_t =
      Bool (** Booleans *)
    | Error (** Error *)
    | Integer (** Infinite-precision integers *)
    | IntType of Expression.t (** Fixed-with signed integers *)
    | BitType of Expression.t (** Fixed-width unsigned integers *)
    | VarBit of Expression.t (** Variable-width integers with a maximum width *)
    | TypeName of P4name.t (** Named types *)
    | SpecializedType of 
        { base: t;
          args: t list } (** Type applications, with a base type and a list of type arguments. *)
    | HeaderStack of 
        { header: t;
          size:  Expression.t } (** Header stacks with a header type and a size *)
    | Tuple of t list (** Tuples *) 
    | String (** Strings *)
    | Void (** Void *)
    | DontCare (** Don't Care (written [_]) *)
  [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]

  val eq : t -> t -> bool
end

(** [MethodPrototype.t] represents a method prototype, which come in three flavors. *)
and MethodPrototype : sig
  type pre_t =
      Constructor of 
        { annotations: Annotation.t list;
          name: P4string.t;
          params: Parameter.t list } (** Constructors, with [annotations], a [name], and [parameters]. *) 
    | AbstractMethod of 
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list} (** Abstract methods, with [annotations], a [return] type, a [name], [type_params], and [params]. *)
    | Method of 
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list} (** Abstract Methods, which also come, with [annotations], a [return] type, a [name], [type_params], and [params]. *)
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Argument.t] rsepresents an argument, which comes in three flavors. *)
and Argument : sig
  type pre_t  =
      Expression of 
        { value: Expression.t } 
    (** Expressions with a [value]. *)
    | KeyValue of 
        { key: P4string.t;
          value: Expression.t }
    (** Key-value pairs with a [key] and a [value]. *)
    | Missing 
    (** Missing (written [_]). *)
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Direction.t] encodes a direction indication for a parameter: [In], [Out], or [InOut]. *)
and Direction : sig
   type pre_t =
       In
     | Out
     | InOut
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Expression.t] represents a P4 expression. *)
and Expression : sig
  type pre_t =
      True (** Boolean [true] literals *)
    | False (** Boolean [false] literal *) 
    | Int of P4int.t (** Integer literal *)
    | String of P4string.t (** String literal *)
    | Name of P4name.t (** Names *)
    | ArrayAccess of 
        { array: t;
          index: t }
    (** Header stack access *)
    | BitStringAccess of        
        { bits: t;
          lo: t;
          hi: t }
    (** Bit slice *)
    | List of
        { values: t list }
    (** Lists *)
    | Record of 
        { entries: KeyValue.t list }
    (** Structs *)
    | UnaryOp of
        { op: Op.uni;
          arg: t }
    (** Unary operations *) 
    | BinaryOp of         
        { op: Op.bin;
          args: (t * t) }
    (** Binary operations *)
    | Cast of 
        { typ: Type.t;
          expr: t }
    (** Type casts *)
    | TypeMember of
        { typ: P4name.t;
          name: P4string.t }
    (** Type members. *)
    | ErrorMember of P4string.t (** Error members *)
    | ExpressionMember of
        { expr: t;
          name: P4string.t }
    (** Expression members *)
    | Ternary of 
        { cond: t;
          tru: t;
          fls: t }
    (** Conditionals *)
    | FunctionCall of 
        { func: t;
          type_args: Type.t list;
          args: Argument.t list }
    (** Function calls. *)
    | NamelessInstantiation of
        { typ: Type.t;
          args: Argument.t list }
    (** Anonymous instantiation *)
    | Mask of 
        { expr: t;
          mask: t }
    (** Bit mask. *)
    | Range of
        { lo: t;
          hi: t }
      (** Ranges *)
  [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Table.t] represents a table declaration *)
and Table : sig
  (** [action_ref] represents action references, with optional [annotations], a [name], and [args]. *)
  type pre_action_ref =
    { annotations: Annotation.t list;
      name: P4name.t;
      args: Argument.t list }
  [@@deriving sexp,show,yojson]

  type action_ref = pre_action_ref info [@@deriving sexp,show,yojson]

  (** [key] represents table keys, with optional [annotations], a [key], and a [match_kind]. *)
  type pre_key =
    { annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4string.t }
  [@@deriving sexp,show,yojson]

  type key = pre_key info [@@deriving sexp,show,yojson]

  (** [entry] represents table entries with optional [annotations], [matches], and an [action]. *)
  type pre_entry =
    { annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }
  [@@deriving sexp,show,yojson { exn = true }]

  type entry = pre_entry info [@@deriving sexp,show,yojson]
 
  (** [property] represents a table property, which come in four flavors. *)
  type pre_property =
      Key of 
        { keys: key list }
      (** Keys *)
    | Actions of
        { actions: action_ref list }
      (** Actions *)
    | Entries of
        { entries: entry list }
    (** Entries *)
    | Custom of
        { annotations: Annotation.t list;
          const: bool;
          name: P4string.t;
          value: Expression.t }
      (** Custom (e.g., [size], [default_action], etc.) *)
        [@@deriving sexp,show,yojson]

  type property = pre_property info [@@deriving sexp,show,yojson]

  val name_of_property : property -> string
end

(** [Match.t] represents pattern matches for [select] statements. *)
and Match : sig
  type pre_t =
      Default (** Default (written [default]). *)
    | DontCare (** Don't care (written [_] and equivalent to [default]. *)
    | Expression of 
        { expr: Expression.t }
          (** Expression with an [expr]. *)
  [@@deriving sexp,show,yojson { exn = true }]

  type t = pre_t info [@@deriving sexp,show,yojson { exn = true }]
end

(** [Parser.t] represents parser declarations *)
and Parser : sig

  (** [case] represents a [select] [case] with [matches] and [next] state. *) 
  type pre_case =
    { matches: Match.t list;
      next: P4string.t }
  [@@deriving sexp,show,yojson { exn = true }]

  type case = pre_case info [@@deriving sexp,show,yojson]

  (** [transition] represents a transition statement, which is either [Direct], with a [next], or a [Select] with [exprs] and [cases]. *)
  type pre_transition =
      Direct of
        { next: P4string.t }
    | Select of
        { exprs: Expression.t list;
          cases: case list }
  [@@deriving sexp,show,yojson]

  type transition = pre_transition info

  (** [state] represents a state with optional [annotations], a [name], [statements], and a [transition]. *)
  type pre_state =
    { annotations: Annotation.t list;
      name: P4string.t;
      statements: Statement.t list;
      transition: transition }
  [@@deriving sexp,show,yojson]

  type state = pre_state info [@@deriving sexp,show,yojson]
end

(** [Declaration.t] represents a top-level declaration *)
and Declaration : sig
  type pre_t =
      Constant of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4string.t;
          value: Expression.t }
    (** Constants *)
    | Instantiation of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4string.t;
          init: Block.t option; }
    (** Instantiation *)
    | Parser of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
    (** Parsers *)
    | Control of 
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
    (** Controls *)
    | Function of
        { return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          body: Block.t }
    (** Functions *)
    | ExternFunction of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    (** Extern function s*) 
    | Variable of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4string.t;
          init: Expression.t option }
    (** Variables *)
    | ValueSet of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          size: Expression.t;
          name: P4string.t }
    (** Parser value sets *)
    | Action of
        { annotations: Annotation.t list;
          name: P4string.t;
          params: Parameter.t list;
          body: Block.t }
    (** Actions *)
    | Table of
        { annotations: Annotation.t list;
          name: P4string.t;
          properties: Table.property list }
    (** Tables *)
    | Header of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    (** Header types *)
    | HeaderUnion of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    (** Header union types *)
    | Struct of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    (** Struct types *)
    | Error of
        { members: P4string.t list }
    (** Error types *)
    | MatchKind of
        { members: P4string.t list }
    (** Match kind types *)
    | Enum of
        { annotations: Annotation.t list;
          name: P4string.t;
          members: P4string.t list }
    (** Enumerated types *)
    | SerializableEnum of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4string.t;
          members: (P4string.t * Expression.t) list }
    (** Serializable enumerated types *)
    | ExternObject of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          methods: MethodPrototype.t list }
    (** Extern objects *)
    | TypeDef of
        { annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
    (** Type definitions *)
    | NewType of
        { annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
    (** Generative type definitions *)
    | ControlType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    (** Control types *) 
    | ParserType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    (** Parser types *)
    | PackageType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
          (** Package types *)
  [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]

  (** [field] represents a field of a [struct], [header], etc. with [annotations], a [typ], and a [name]. *)
  and pre_field =
      { annotations: Annotation.t list;
        typ: Type.t [@key "type"];
        name: P4string.t } [@@deriving sexp,show,yojson]

  and field = pre_field info [@@deriving sexp,show,yojson]

  val name : t -> P4string.t

  val name_opt : t -> P4string.t option
end

(** [Statement.t] represents a P4 statement *)
and Statement : sig
  (** [switch_label] represents the label on a switch statement, which is either [default] or a [name] *)
  type pre_switch_label =
      Default
    | Name of P4string.t
  [@@deriving sexp,show,yojson]

  type switch_label = pre_switch_label info [@@deriving sexp,show,yojson]

  (** [switch case] represents a case of a switch statement, which is either an [Action] with a [label]ed block of [code], or a [FallThrough] with just a [label]. *)
  type pre_switch_case =
    Action of
      { label: switch_label;
        code: Block.t }
  | FallThrough of
      { label: switch_label }
  [@@deriving sexp,show,yojson]

  type switch_case = pre_switch_case info [@@deriving sexp,show,yojson]

  (** [Statement.t] comes in 10 flavors. *) 
  type pre_t =
      MethodCall of
      { func: Expression.t;
        type_args: Type.t list;
        args: Argument.t list }
    (** Method call *)
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t }
    (** Assignment *)
    | DirectApplication of
        { typ: Type.t;
          args: Argument.t list }
    (** Direct application *)
    | Conditional of
        { cond: Expression.t;
          tru: t;
          fls: t option }
    (** If-Then-Else *)
    | BlockStatement of
        { block: Block.t }
    (** Block statement *)
    | Exit (** Exit *)
    | EmptyStatement (** Empty (written [;]) *)
    | Return of
        { expr: Expression.t option }
    (** Return *)
    | Switch of
        { expr: Expression.t;
          cases: switch_case list }
    (** Switch *)
    | DeclarationStatement of
        { decl: Declaration.t }
    (** Declaration *)
  [@@deriving sexp,show,yojson]

  and t = pre_t info [@@deriving sexp,show,yojson]
end

(** [Block.t] represents a block of statements, with [annotations] and a list of [statements]. *) 
and Block : sig
  type pre_t =
    { annotations: Annotation.t list;
      statements: Statement.t list }
  [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end

(** [program] represents a P4 program with a [Declaration.t] list. *)
type program =
  Program of Declaration.t list [@@deriving sexp,show,yojson]
