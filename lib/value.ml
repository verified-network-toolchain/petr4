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
  | VPackage of 
      { decl : Declaration.t;
        args : (string * value) list; }
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
  | LMember of 
    { expr : lvalue;
      name : string; }
  | LBitAccess of 
      { expr : lvalue;
        msb : Expression.t;
        lsb : Expression.t; }
  | LArrayAccess of 
      { expr : lvalue;
        idx : Expression.t; }

and set =
  | SSingleton of 
      { w : Bigint.t;
        v : Bigint.t; }
  | SUniversal
  | SMask of 
      { v : value;
        mask : value; }
  | SRange of 
      { lo : value;
        hi : value; }
  | SProd of set list
  | SLpm of 
      { w : value;
        nbits : Bigint.t;
        v : value; }
  | SValueSet of 
      { size : value;
        members : Match.t list list;
        sets : set list; }

and signal =
  | SContinue
  | SReturn of value
  | SExit
  | SReject

and vruntime =
  | PacketIn of packet_in
  | PacketOut of packet_out
  
