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

(** [KeyValue.t] represents a key-value pair; the key is a [P4string.t] and the value is an [Expression.t]  *)
module rec KeyValue : sig
  type 'a pt =
    { tags: 'a;
      key : P4string.t;
      value : Expression.t }

  type t = P4info.t pt
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
          str: P4string.t list}
    | Expression of 
        { tags: 'a; 
          exprs: Expression.t list}
    | KeyValue of 
        { tags: 'a; 
          k_v: KeyValue.t list} 

  type body = P4info.t pbody

  type 'a pt =
    { tags: 'a;
      name: P4string.t;
      body: body }

  type t = P4info.t pt
end

(** [Parameter.t] represents a parameter, with an optional list of [annotations], 
    an optional [direction], a [typ], a [variable], and an optional [opt_value]. *)
and Parameter : sig
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4string.t;
      opt_value: Expression.t option}

  type t = P4info.t pt
end

(** [Op.t] represents operators, which are either [uni] or [bin], 
    for unary and binary respectively. *)
and Op : sig
  type 'a puni =
      Not of {tags: 'a}
    | BitNot of {tags: 'a}
    | UMinus of {tags: 'a}
  

  type uni = P4info.t puni 

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
  

  type bin = P4info.t pbin 

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
      (** Fixed-width signed integers *)
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
          name: P4name.t} 
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
  

  and t = P4info.t pt 
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
          name: P4string.t;
          params: Parameter.t list } 
      (** Constructors, with [annotations], a [name], and [parameters]. *) 
    | AbstractMethod of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list} 
      (** Abstract methods, with [annotations], a [return] type, a [name], 
          [type_params], and [params]. *)
    | Method of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list} 
      (** Abstract Methods, which also come, with [annotations], 
          a [return] type, a [name], [type_params], and [params]. *)
  

  type t = P4info.t pt 
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
          key: P4string.t;
          value: Expression.t }
      (** Key-value pairs with a [key] and a [value]. *)
    | Missing of {tags: 'a}
      (** Missing (written [_]). *)
  

  type t = P4info.t pt 
end

(** [Direction.t] encodes a direction indication for a parameter: [In], [Out], 
    or [InOut]. *)
and Direction : sig
   type 'a pt =
      In of {tags: 'a}
    | Out of {tags: 'a}
    | InOut of {tags: 'a}
  

  type t = P4info.t pt 

  val tags : 'a pt -> 'a 
end

(** [Expression.t] represents a P4 expression. *)
and Expression : sig
  type 'a pt =
      True of {tags: 'a} (** Boolean [true] literals *)
    | False of {tags: 'a} (** Boolean [false] literal *) 
    | Int of 
        { tags: 'a;
          x: P4int.t}
      (** Integer literal *)
    | String of 
        { tags: 'a;
          str: P4string.t}
      (** String literal *)
    | Name of 
        { tags: 'a;
          name: P4name.t}
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
          typ: P4name.t;
          name: P4string.t }
      (** Type members. *)
    | ErrorMember of 
        {tags: 'a;
         err: P4string.t}
      (** Error members *)
    | ExpressionMember of
        { tags: 'a;
          expr: t;
          name: P4string.t }
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
          typ: Type.t ;
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

  and t = P4info.t pt 
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
      name: P4name.t;
      args: Argument.t list }

  type action_ref = P4info.t paction_ref 

  (** [key] represents table keys, with optional [annotations], a [key], 
      and a [match_kind]. *)
  type 'a pkey =
    { tags: 'a;
      annotations: Annotation.t list;
      key: Expression.t;
      match_kind: P4string.t }

  type key = P4info.t pkey 

  (** [entry] represents table entries with optional [annotations], [matches], 
      and an [action]. *)
  type 'a pentry =
    { tags: 'a;
      annotations: Annotation.t list;
      matches: Match.t list;
      action: action_ref }

  type entry = P4info.t pentry 

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
    | DefaultAction of
        { tags: 'a;
          action: action_ref;
          const: bool }
      (** Default actions *)
    | Custom of
        { tags: 'a;
          annotations: Annotation.t list;
          const: bool;
          name: P4string.t;
          value: Expression.t }
      (** Custom (e.g., [size], etc.) *)
  

  type property = P4info.t pproperty 

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
  

  type t = P4info.t pt 

  val tags : 'a pt -> 'a
  
end

(** [Parser.t] represents parser declarations *)
and Parser : sig

  (** [case] represents a [select] [case] with [matches] and [next] state. *) 
  type 'a pcase =
    { tags: 'a; 
      matches: Match.t list;
      next: P4string.t }
  

  type case = P4info.t pcase 
  
  (** [transition] represents a transition statement, which is either [Direct],
      with a [next], or a [Select] with [exprs] and [cases]. *)
  type 'a ptransition =
      Direct of
        { tags: 'a;
          next: P4string.t }
    | Select of
        { tags: 'a;
          exprs: Expression.t list;
          cases: case list }

  type transition = P4info.t ptransition 

  (** [state] represents a state with optional [annotations], a [name], 
      [statements], and a [transition]. *)
  type 'a pstate =
    { tags: 'a;
      annotations: Annotation.t list;
      name: P4string.t;
      statements: Statement.t list;
      transition: transition }

  type state = P4info.t pstate 

  val transition_tags : 'a ptransition -> 'a

  val update_transition_tags : 'a ptransition -> 'a -> 'a ptransition
end

(** [Declaration.t] represents a top-level declaration *)
and Declaration : sig
  type 'a pt =
      Constant of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t ;
          name: P4string.t;
          value: Expression.t }
      (** Constants *)
    | Instantiation of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t ;
          args: Argument.t list;
          name: P4string.t;
          init: Block.t option; }
      (** Instantiation *)
    | Parser of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
      (** Parsers *)
    | Control of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
      (** Controls *)
    | Function of
        { tags: 'a;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          body: Block.t }
      (** Functions *)
    | ExternFunction of
        { tags: 'a;
          annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
      (** Extern functions *) 
    | Variable of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t ;
          name: P4string.t;
          init: Expression.t option }
      (** Variables *) 
    | ValueSet of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t ;
          size: Expression.t;
          name: P4string.t }
      (** Parser value sets *)
    | Action of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          params: Parameter.t list;
          body: Block.t }
      (** Actions *)
    | Table of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          properties: Table.property list }
      (** Tables *)
    | Header of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
      (** Header types *)
    | HeaderUnion of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
      (** Header union types *)
    | Struct of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
      (** Struct types *)
    | Error of
        { tags: 'a;
          members: P4string.t list }
      (** Error types *)
    | MatchKind of
        { tags: 'a;
          members: P4string.t list }
      (** Match kind types *)
    | Enum of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          members: P4string.t list }
      (** Enumerated types *)
    | SerializableEnum of
        { tags: 'a;
          annotations: Annotation.t list;
          typ: Type.t ;
          name: P4string.t;
          members: (P4string.t * Expression.t) list }
      (** Serializable enumerated types *)
    | ExternObject of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          methods: MethodPrototype.t list }
      (** Extern objects *)
    | TypeDef of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
      (** Type definitions *)
    | NewType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
      (** Generative type definitions *)
    | ControlType of
        { tags:'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
      (** Control types *) 
    | ParserType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
      (** Parser types *)
    | PackageType of
        { tags: 'a;
          annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
      (** Package types *)
  

  and t = P4info.t pt 

  (** [field] represents a field of a [struct], [header], etc. 
      with [annotations], a [typ], and a [name]. *)
  and 'a pfield =
    { tags: 'a;
      annotations: Annotation.t list;
      typ: Type.t ;
      name: P4string.t } 

  and field = P4info.t pfield 

  val name : t -> P4string.t

  val name_opt : t -> P4string.t option

  val tags : 'a pt -> 'a

end

(** [Statement.t] represents a P4 statement *)
and Statement : sig
  
  (** [switch_label] represents the label on a switch statement, which is 
      either [default] or a [name] *)
  type 'a pswitch_label =
      Default of {tags: 'a}
    | Name of 
        { tags: 'a;
          name: P4string.t}
  

  type switch_label = P4info.t pswitch_label 

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
  

  type switch_case = P4info.t pswitch_case 

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
          typ: Type.t ;
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
  

  and t = P4info.t pt 

  val tags : 'a pt -> 'a

end

(** [Block.t] represents a block of statements, with [annotations] and a list of [statements]. *) 
and Block : sig
  type 'a pt =
    { tags: 'a;
      annotations: Annotation.t list;
      statements: Statement.t list }

  type t = P4info.t pt 

end

(** [program] represents a P4 program with a [Declaration.t] list. *)
type program =
  Program of Declaration.t list
