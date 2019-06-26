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
  | VMatchKind
  | VFun of Parameter.t list * Block.t
  | VAction of Parameter.t list * Block.t
  | VStruct of string * (string * value) list
  | VHeader of string * (string * value) list * bool
  | VEnumField of string * string
  | VExternFun of Parameter.t list
  | VExternObject of string * (MethodPrototype.t list)
  | VRuntime of string
  | VObjstate of Declaration.t * (string * value) list
  (* stateful objects *)

and set =
  | SSingleton of Bigint.t
  | SUniversal
  | SMask of value * value
  | SRange of value * value
  | SProd

type signal =
  | SContinue
  | SReturn of value
  | SExit
