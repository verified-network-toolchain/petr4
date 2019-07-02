open Types

type value =
  | VNull
  | VBool of bool
  | VInteger of Bigint.t
  | VBit of int * Bigint.t
  | VInt of int * Bigint.t
  | VTuple of value list
  | VSet of set
  | VString of string
  | VError of string
  | VMatchKind
  | VFun of Parameter.t list * Block.t
  | VBuiltinFun of string * lvalue
  | VAction of Parameter.t list * Block.t
  | VStruct of string * (string * value) list
  | VHeader of string * (string * value) list * bool
  | VUnion of string * value * (string * bool) list
  | VStack of string * value list * int * int
  | VEnumField of string * string
  | VExternFun of Parameter.t list
  | VExternObject of string * (MethodPrototype.t list)
  | VRuntime of vruntime
  | VObjstate of Declaration.t * (string * value) list

and lvalue =
  | LName of string
  | LTopName of string
  | LMember of lvalue * string
  | LBitAccess of lvalue * Expression.t * Expression.t
  | LArrayAccess of lvalue * Expression.t

and set =
  | SSingleton of Bigint.t
  | SUniversal
  | SMask of value * value
  | SRange of value * value
  | SProd

and vruntime =
  | Packet of packet

and signal =
  | SContinue
  | SReturn of value
  | SExit

and packet = Bigint.t
