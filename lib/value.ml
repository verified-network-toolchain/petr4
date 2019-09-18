open Types

module rec Value : sig

  type packet_in = Cstruct.t

  type packet_out = Cstruct.t * Cstruct.t

  type value =
    | VNull
    | VBool of bool
    | VInteger of Bigint.t
    | VBit of Bigint.t * Bigint.t
    | VInt of Bigint.t * Bigint.t
    | VVarbit of Bigint.t * Bigint.t * Bigint.t (* max width, dynamic width, value*)
    | VTuple of value list
    | VSet of set
    | VString of string
    | VError of string
    | VMatchKind
    | VFun of Parameter.t list * Block.t
    | VBuiltinFun of string * lvalue
    | VAction of Parameter.t list * Block.t
    | VStruct of string * (string * value ) list
    | VHeader of string * (string * value ) list * bool
    | VUnion of string * value * (string * bool) list
    | VStack of string * value list * Bigint.t * Bigint.t
    | VEnumField of string * string
    | VSenumField of string * string * value 
    | VExternFun of Parameter.t list
    | VExternObject of string * (MethodPrototype.t list)
    | VRuntime of vruntime
    | VParser of parserv
    | VControl of controlv
    | VPackage of Declaration.t * (string * value ) list
    | VTable of TableV.t

    and parserv = {
      pvs : (string * value) list;
      pparams : Parameter.t list;
      plocals : Declaration.t list;
      states : Parser.state list;
    }
  
    and controlv = {
      cvs : (string * value) list;
      cparams : Parameter.t list;
      clocals : Declaration.t list;
      apply : Block.t;
    }

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
      | SProd of set list

    and signal =
      | SContinue
      | SReturn of value
      | SExit
      | SReject

    and vruntime =
      | PacketIn of packet_in
      | PacketOut of packet_out
end = struct 

  type packet_in = Cstruct.t

  type packet_out = Cstruct.t * Cstruct.t

  type value =
    | VNull
    | VBool of bool
    | VInteger of Bigint.t
    (* width, value *)
    | VBit of Bigint.t * Bigint.t
    (* width value *)
    | VInt of Bigint.t * Bigint.t
    (* max width, dynamic width, value *)
    | VVarbit of Bigint.t * Bigint.t * Bigint.t
    | VTuple of value list
    | VSet of set
    | VString of string
    | VError of string
    | VMatchKind
    | VFun of Parameter.t list * Block.t
    | VBuiltinFun of string * lvalue
    | VAction of Parameter.t list * Block.t
    | VStruct of string * (string * value ) list
    | VHeader of string * (string * value ) list * bool
    | VUnion of string * value * (string * bool) list
    | VStack of string * value list * Bigint.t * Bigint.t
    | VEnumField of string * string
    | VSenumField of string * string * value 
    | VExternFun of Parameter.t list
    | VExternObject of string * (MethodPrototype.t list)
    | VRuntime of vruntime
    | VParser of parserv
    | VControl of controlv
    | VPackage of Declaration.t * (string * value ) list
    | VTable of TableV.t

    and parserv = {
      pvs : (string * value) list;
      pparams : Parameter.t list;
      plocals : Declaration.t list;
      states : Parser.state list;
    }
  
    and controlv = {
      cvs : (string * value) list;
      cparams : Parameter.t list;
      clocals : Declaration.t list;
      apply : Block.t;
    }

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
    | SProd of set list

  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject

  and vruntime =
    | PacketIn of packet_in
    | PacketOut of packet_out
  
  end


  and TableV : sig
    type entry 
    type t = Value.value list * entry list
    val empty : t
    val add : Value.set -> string -> t -> t
    val table_of_entries : Table.entry list -> entry list
  end = struct 
    type entry = Value.set * string
    type t = Value.value list * entry list 
    let empty = ([],[]) 
    let add (key : Value.set) (action : string) (table : t) : t = 
      let (a,b) = table in 
      (a, (key, action) :: b)
    let table_of_entries l = []
  end 
  