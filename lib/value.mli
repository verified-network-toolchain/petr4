open Types

type packet_in = Cstruct.t

type packet_out = Cstruct.t * Cstruct.t

type value =
  | VNull
  | VBool of bool
  | VInteger of Bigint.t
  | VBit of 
      { w : Bigint.t;
        v : Bigint.t; }
  | VInt of 
      { w : Bigint.t;
        v : Bigint.t; }
  | VVarbit of 
      { max : Bigint.t;
        w : Bigint.t;
        v : Bigint.t; }
  | VString of string
  | VTuple of value list
  | VSet of set
  | VError of string
  | VFun of 
      { params : Parameter.t list;
        body : Block.t; }
  | VBuiltinFun of 
      { name : string;
        caller : lvalue; }
  | VAction of 
      { params : Parameter.t list;
        body : Block.t; }
  | VStruct of 
      { name : string;
        fields : (string * value) list; }
  | VHeader of 
      { name : string;
        fields : (string * value) list;
        is_valid : bool }
  | VUnion of 
      { name : string;
        valid_header : value;
        valid_fields : (string * bool) list; }
  | VStack of 
      { name : string;
        headers : value list;
        size : Bigint.t;
        next : Bigint.t; }
  | VEnumField of 
      { typ_name : string;
        enum_name : string; }
  | VSenumField of 
      { typ_name : string;
        enum_name : string;
        v : value; }
  | VRuntime of vruntime
  | VParser of vparser
  | VControl of vcontrol
  | VPackage of Declaration.t * (string * value) list
  | VTable of vtable

  and vparser = {
    pvs : (string * value) list;
    pparams : Parameter.t list;
    plocals : Declaration.t list;
    states : Parser.state list;
  }

  and vcontrol = {
    cvs : (string * value) list;
    cparams : Parameter.t list;
    clocals : Declaration.t list;
    apply : Block.t;
  }

  and vtable = {
    name : string;
    keys : value list;
    actions : Table.action_ref list;
    default_action : Table.action_ref;
    const_entries : (set * Table.action_ref) list;
  }

  and lvalue =
    | LName of string
    | LTopName of string
    | LMember of lvalue * string
    | LBitAccess of lvalue * Expression.t * Expression.t
    | LArrayAccess of lvalue * Expression.t

  and set =
    | SSingleton of Bigint.t * Bigint.t
    | SUniversal
    | SMask of value * value
    | SRange of value * value
    | SProd of set list
    | SLpm of value * Bigint.t * value
    | SValueSet of value * Parser.case list

  and signal =
    | SContinue
    | SReturn of value
    | SExit
    | SReject

  and vruntime =
    | PacketIn of packet_in
    | PacketOut of packet_out
