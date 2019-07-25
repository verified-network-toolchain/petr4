open Types

type 'a pre_value =
  | VNull
  | VBool of bool
  | VInteger of Bigint.t
  | VBit of Bigint.t * Bigint.t
  | VInt of Bigint.t * Bigint.t
  | VVarbit of Bigint.t * Bigint.t
  | VTuple of 'a pre_value list
  | VSet of 'a pre_set
  | VString of string
  | VError of string
  | VMatchKind
  | VFun of Parameter.t list * Block.t
  | VBuiltinFun of string * lvalue
  | VAction of Parameter.t list * Block.t
  | VStruct of string * (string * 'a pre_value) list
  | VHeader of string * (string * 'a pre_value) list * bool
  | VUnion of string * 'a pre_value * (string * bool) list
  | VStack of string * 'a pre_value list * Bigint.t * Bigint.t
  | VEnumField of string * string
  | VSenumField of string * string * 'a pre_value
  | VExternFun of Parameter.t list
  | VExternObject of string * (MethodPrototype.t list)
  | VRuntime of 'a pre_vruntime
  | VObjstate of Declaration.t * (string * 'a pre_value) list

and lvalue =
  | LName of string
  | LTopName of string
  | LMember of lvalue * string
  | LBitAccess of lvalue * Expression.t * Expression.t
  | LArrayAccess of lvalue * Expression.t

and 'a pre_set =
  | SSingleton of Bigint.t
  | SUniversal
  | SMask of 'a pre_value * 'a pre_value
  | SRange of 'a pre_value * 'a pre_value
  | SProd of 'a pre_set list

and 'a pre_signal =
  | SContinue
  | SReturn of 'a pre_value
  | SExit
  | SReject

and 'a pre_vruntime =
  | Packet of 'a
