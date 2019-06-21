open Types

type value =
  | VNull
  | VBool of bool
  | VInteger of Bigint.t
  | VBit of int * Bigint.t (* width, value *)
  | VInt of int * Bigint.t
  | VTuple of value list
  | VSet of set
  | VString of string
  | VError of string
  | VFun of Parameter.t list * Block.t
  | VStruct of (string * value) list
  | VHeader of string * (string * value) list * bool
  | VObjstate of obj
  (* stateful objects *)

and set =
  | SSingleton of Bigint.t
  | SUniversal
  | SMask of value * value
  | SRange of value * value
  | SProd

and obj =
  { decl: Types.Declaration.t;
    state: (P4String.t * value) list; }

type signal =
  | SContinue
  | SReturn of value
  | SExit
