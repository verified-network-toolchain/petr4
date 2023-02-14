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

type 'a info = P4info.t * 'a

let info (i,_) = i

let info_to_yojson f (_,x) = f x

let info_of_yojson f json =
  match f json with
  | Ok pre -> Ok (P4info.M "<yojson>", pre)
  | Error x -> Error x

module rec KeyValue : sig
  type pre_t =
    { key : P4string.t;
      value : Expression.t }

  type t = pre_t info
end = struct
  type pre_t =
    { key : P4string.t;
      value : Expression.t }

  type t = pre_t info
end

and Annotation : sig
  type pre_body =
    | Empty
    | Unparsed of P4string.t list
    | Expression of Expression.t list
    | KeyValue of KeyValue.t list

  type body = pre_body info

  type pre_t =
    { name: P4string.t;
      body: body }

  type t = pre_t info
end = struct
  type pre_body =
    | Empty
    | Unparsed of P4string.t list
    | Expression of Expression.t list
    | KeyValue of KeyValue.t list

  type body = pre_body info

  type pre_t =
    { name: P4string.t;
      body: body }

  type t = pre_t info
end

and Parameter : sig
  type pre_t =
    { annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4string.t;
      opt_value: Expression.t option}

  type t = pre_t info
end = struct
  type pre_t =
    { annotations: Annotation.t list;
      direction: Direction.t option;
      typ: Type.t;
      variable: P4string.t;
      opt_value: Expression.t option}

  type t = pre_t info
end

and Op : sig
  type pre_uni =
      Not
    | BitNot
    | UMinus

  type uni = pre_uni info

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

  type bin = pre_bin info

  val eq_bin : bin -> bin -> bool
end = struct
  type pre_uni =
      Not
    | BitNot
    | UMinus

  type uni = pre_uni info

  let eq_uni (_,u1) (_,u2) =
    match u1,u2 with
    | Not, Not
    | BitNot, BitNot
    | UMinus, UMinus -> true
    | _ -> false

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

  type bin = pre_bin info

  let eq_bin (_,b1) (_,b2) =
    match b1,b2 with
    | Plus, Plus
    | PlusSat, PlusSat
    | Minus, Minus
    | MinusSat, MinusSat
    | Mul, Mul
    | Div, Div
    | Mod, Mod
    | Shl, Shl
    | Shr, Shr
    | Le, Le
    | Ge, Ge
    | Lt, Lt
    | Gt, Gt
    | Eq, Eq
    | NotEq, NotEq
    | BitAnd, BitAnd
    | BitXor, BitXor
    | BitOr, BitOr
    | PlusPlus, PlusPlus
    | And, And
    | Or, Or -> true
    | _ -> false
end

and Type : sig
  type pre_t =
      Bool
    | Error
    | Integer
    | IntType of Expression.t
    | BitType of Expression.t
    | VarBit of Expression.t
    (* this could be a typename or a type variable. *)
    | TypeName of P4name.t
    | SpecializedType of
        { base: t;
          args: t list }
    | HeaderStack of
        { header: t;
          size:  Expression.t }
    | Tuple of t list
    | String
    | Void
    | DontCare

  and t = pre_t info

  val eq : t -> t -> bool
end = struct
  type pre_t =
      Bool
    | Error
    | Integer
    | IntType of Expression.t
    | BitType of Expression.t 
    | VarBit of Expression.t 
    | TypeName of P4name.t
    | SpecializedType of
        { base: t;
          args: t list }
    | HeaderStack of
        { header: t;
          size:  Expression.t }
    | Tuple of t list
    | String
    | Void
    | DontCare

  and t = pre_t info

  let rec eq (_,t1) (_,t2) =
    match t1, t2 with
    | Bool, Bool
    | Error, Error
    | Integer, Integer
    | String, String
    | Void, Void
    | DontCare, DontCare -> true
    | IntType e1, IntType e2 -> failwith "TODO"
    | BitType e1, BitType e2 -> failwith "TODO"
    | VarBit e1, VarBit e2 -> failwith "TODO"
    | TypeName n1, TypeName n2 ->
      P4name.name_eq n1 n2
    | SpecializedType { base=b1; args=a1 },
      SpecializedType { base=b2; args=a2 }
      -> eq b1 b2 &&
        begin match Base.List.for_all2 a1 a2 ~f:eq with
        | Ok tf -> tf
        | Unequal_lengths -> false
        end
    | HeaderStack { header=h1; size=s1 },
      HeaderStack { header=h2; size=s2 }
      -> eq h1 h2 && failwith "TODO"
    | Tuple t1, Tuple t2 ->
      begin match Base.List.for_all2 t1 t2 ~f:eq with
      | Ok tf -> tf
      | Unequal_lengths -> false
      end
    | _ -> false
end

and MethodPrototype : sig
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4string.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4string.t;
        type_params: P4string.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4string.t;
        type_params: P4string.t list;
        params: Parameter.t list}

  type t = pre_t info
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4string.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4string.t;
        type_params: P4string.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4string.t;
        type_params: P4string.t list;
        params: Parameter.t list}

  type t = pre_t info
end

and Argument : sig
      type pre_t  =
          Expression of
            { value: Expression.t }
        | KeyValue of
            { key: P4string.t;
              value: Expression.t }
        | Missing

      type t = pre_t info
    end = struct
                 type pre_t  =
                     Expression of
                       { value: Expression.t }
                   | KeyValue of
                       { key: P4string.t;
                         value: Expression.t }
                   | Missing

                 type t = pre_t info
               end

and Direction : sig
      type pre_t =
          In
        | Out
        | InOut

      type t = pre_t info
    end = struct
                  type pre_t =
                      In
                    | Out
                    | InOut

                  type t = pre_t info
                end

and Expression : sig
      type pre_t =
          True
        | False
        | Int of P4int.t
        | String of P4string.t
        | Name of P4name.t
        | ArrayAccess of
            { array: t;
              index: t }
        | BitStringAccess of
            { bits: t;
              lo: t;
              hi: t }
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
            { typ: P4name.t;
              name: P4string.t }
        | ErrorMember of P4string.t
        | ExpressionMember of
            { expr: t;
              name: P4string.t }
        | Ternary of
            { cond: t;
              tru: t;
              fls: t }
        | FunctionCall of
            { func: t;
              type_args: Type.t list;
              args: Argument.t list }
        | NamelessInstantiation of
            { typ: Type.t;
              args: Argument.t list }
        | Mask of
            { expr: t;
              mask: t }
        | Range of
            { lo: t;
              hi: t }

      and t = pre_t info
end = struct
  type pre_t =
      True
    | False 
    | Int of P4int.t 
    | String of P4string.t
    | Name of P4name.t
    | ArrayAccess of
        { array: t;
          index: t }
    | BitStringAccess of
        { bits: t;
          lo: t;
          hi: t }
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
        { typ: P4name.t;
          name: P4string.t }
    | ErrorMember of P4string.t
    | ExpressionMember of
        { expr: t;
          name: P4string.t }
    | Ternary of
        { cond: t;
          tru: t;
          fls: t }
    | FunctionCall of
        { func: t;
          type_args: Type.t list;
          args: Argument.t list }
    | NamelessInstantiation of
        { typ: Type.t;
          args: Argument.t list }
    | Mask of
        { expr: t;
          mask: t }
    | Range of
        { lo: t;
          hi: t }

  and t = pre_t info
end

and Table : sig
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: P4name.t;
          args: Argument.t list }

      type action_ref = pre_action_ref info

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: P4string.t }

      type key = pre_key info

      type pre_entry =
        { annotations: Annotation.t list;
          matches: Match.t list;
          action: action_ref }

      type entry = pre_entry info

      type pre_property =
          Key of
            { keys: key list }
        | Actions of
            { actions: action_ref list }
        | Entries of
            { entries: entry list }
        | DefaultAction of action_ref
        | Custom of
            { annotations: Annotation.t list;
              const: bool;
              name: P4string.t;
              value: Expression.t }

      type property = pre_property info

      val name_of_property : property -> string
    end = struct
              type pre_action_ref =
                { annotations: Annotation.t list;
                  name: P4name.t;
                  args: Argument.t list }

              type action_ref = pre_action_ref info

              type pre_key =
                { annotations: Annotation.t list;
                  key: Expression.t;
                  match_kind: P4string.t }

              type key = pre_key info

              type pre_entry =
                { annotations: Annotation.t list;
                  matches: Match.t list;
                  action: action_ref }

              type entry = pre_entry info

              type pre_property =
                  Key of
                    { keys: key list }
                | Actions of
                    { actions: action_ref list }
                | Entries of
                    { entries: entry list }
                | DefaultAction of action_ref
                | Custom of
                    { annotations: Annotation.t list;
                      const: bool;
                      name: P4string.t;
                      value: Expression.t }

              type property = pre_property info

              let name_of_property p =
                match snd p with
                | Key _ -> "key"
                | Actions _ -> "actions"
                | Entries _ -> "entries"
                | DefaultAction _ -> "default_action"
                | Custom {name; _} -> name.str
            end

and Match : sig
      type pre_t =
          Default
        | DontCare
        | Expression of
            { expr: Expression.t }

      type t = pre_t info
    end = struct
              type pre_t =
                  Default
                | DontCare
                | Expression of
                    { expr: Expression.t }

              type t = pre_t info
            end

and Parser : sig
      type pre_case =
        { matches: Match.t list;
          next: P4string.t }

      type case = pre_case info

      type pre_transition =
          Direct of
            { next: P4string.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }

      type transition = pre_transition info

      type pre_state =
        { annotations: Annotation.t list;
          name: P4string.t;
          statements: Statement.t list;
          transition: transition }

      type state = pre_state info
    end = struct
               type pre_case =
                 { matches: Match.t list;
                   next: P4string.t }

               type case = pre_case info

               type pre_transition =
                   Direct of
                     { next: P4string.t }
                 | Select of
                     { exprs: Expression.t list;
                       cases: case list }

               type transition = pre_transition info

               type pre_state =
                 { annotations: Annotation.t list;
                   name: P4string.t;
                   statements: Statement.t list;
                   transition: transition }

               type state = pre_state info
             end

and Declaration : sig
      type pre_t =
          Constant of
            { annotations: Annotation.t list;
              typ: Type.t;
              name: P4string.t;
              value: Expression.t }
        | Instantiation of
            { annotations: Annotation.t list;
              typ: Type.t;
              args: Argument.t list;
              name: P4string.t;
              init: Block.t option; }
        | Parser of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list;
              constructor_params: Parameter.t list;
              locals: t list;
              states: Parser.state list }
        | Control of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list;
              constructor_params: Parameter.t list;
              locals: t list;
              apply: Block.t }
        | Function of
            { return: Type.t;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list;
              body: Block.t }
        | ExternFunction of
            { annotations: Annotation.t list;
              return: Type.t;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list }
        | Variable of
            { annotations: Annotation.t list;
              typ: Type.t;
              name: P4string.t;
              init: Expression.t option }
        | ValueSet of
            { annotations: Annotation.t list;
              typ: Type.t;
              size: Expression.t;
              name: P4string.t }
        | Action of
            { annotations: Annotation.t list;
              name: P4string.t;
              params: Parameter.t list;
              body: Block.t }
        | Table of
            { annotations: Annotation.t list;
              name: P4string.t;
              properties: Table.property list }
        | Header of
            { annotations: Annotation.t list;
              name: P4string.t;
              fields: field list }
        | HeaderUnion of
            { annotations: Annotation.t list;
              name: P4string.t;
              fields: field list }
        | Struct of
            { annotations: Annotation.t list;
              name: P4string.t;
              fields: field list }
        | Error of
            { members: P4string.t list }
        | MatchKind of
            { members: P4string.t list }
        | Enum of
            { annotations: Annotation.t list;
              name: P4string.t;
              members: P4string.t list }
        | SerializableEnum of
            { annotations: Annotation.t list;
              typ: Type.t;
              name: P4string.t;
              members: (P4string.t * Expression.t) list }
        | ExternObject of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              methods: MethodPrototype.t list }
        | TypeDef of
            { annotations: Annotation.t list;
              name: P4string.t;
              typ_or_decl: (Type.t, t) alternative }
        | NewType of
            { annotations: Annotation.t list;
              name: P4string.t;
              typ_or_decl: (Type.t, t) alternative }
        | ControlType of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list }
        | ParserType of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list }
        | PackageType of
            { annotations: Annotation.t list;
              name: P4string.t;
              type_params: P4string.t list;
              params: Parameter.t list }

and t = pre_t info

and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t;
      name: P4string.t }

and field = pre_field info

val name : t -> P4string.t

val name_opt : t -> P4string.t option

end = struct
  type pre_t =
      Constant of
        { annotations: Annotation.t list;
          typ: Type.t;
          name: P4string.t;
          value: Expression.t }
    | Instantiation of
        { annotations: Annotation.t list;
          typ: Type.t;
          args: Argument.t list;
          name: P4string.t;
          init: Block.t option; }
    | Parser of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
    | Control of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }

    | Function of
        { return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    | Variable of
        { annotations: Annotation.t list;
          typ: Type.t;
          name: P4string.t;
          init: Expression.t option }
    | ValueSet of
        { annotations: Annotation.t list;
          typ: Type.t;
          size: Expression.t;
          name: P4string.t }
    | Action of
        { annotations: Annotation.t list;
          name: P4string.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { annotations: Annotation.t list;
          name: P4string.t;
          properties: Table.property list }
    | Header of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    | HeaderUnion of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    | Struct of
        { annotations: Annotation.t list;
          name: P4string.t;
          fields: field list }
    | Error of
        { members: P4string.t list }
    | MatchKind of
        { members: P4string.t list }
    | Enum of
        { annotations: Annotation.t list;
          name: P4string.t;
          members: P4string.t list }
    | SerializableEnum of
        { annotations: Annotation.t list;
          typ: Type.t;
          name: P4string.t;
          members: (P4string.t * Expression.t) list }
    | ExternObject of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { annotations: Annotation.t list;
          name: P4string.t;
          typ_or_decl: (Type.t, t) alternative }
    | ControlType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    | ParserType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }
    | PackageType of
        { annotations: Annotation.t list;
          name: P4string.t;
          type_params: P4string.t list;
          params: Parameter.t list }

and t = pre_t info

and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t;
      name: P4string.t }

and field = pre_field info

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

and Statement : sig
      type pre_switch_label =
          Default
        | Name of P4string.t


      type switch_label = pre_switch_label info

      type pre_switch_case =
          Action of
            { label: switch_label;
              code: Block.t }
        | FallThrough of
            { label: switch_label }


      type switch_case = pre_switch_case info

      type pre_t =
          MethodCall of
            { func: Expression.t;
              type_args: Type.t list;
              args: Argument.t list }
        | Assignment of
            { lhs: Expression.t;
              rhs: Expression.t }
        | DirectApplication of
            { typ: Type.t;
              args: Argument.t list }
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

and t = pre_t info
end = struct
  type pre_switch_label =
      Default
    | Name of P4string.t


  type switch_label = pre_switch_label info

  type pre_switch_case =
      Action of
        { label: switch_label;
          code: Block.t }
    | FallThrough of
        { label: switch_label }

  type switch_case = pre_switch_case info

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list }
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t }
    | DirectApplication of
        { typ: Type.t;
          args: Argument.t list }
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

and t = pre_t info
end

and Block : sig
      type pre_t =
        { annotations: Annotation.t list;
          statements: Statement.t list }

      type t = pre_t info
    end = struct
              type pre_t =
                { annotations: Annotation.t list;
                  statements: Statement.t list }

              type t = pre_t info
            end

type program =
    Program of Declaration.t list

