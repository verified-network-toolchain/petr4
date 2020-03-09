open Types

type pkt = Cstruct_sexp.t [@@deriving sexp]

type pkt_out = Cstruct_sexp.t * Cstruct_sexp.t [@@deriving sexp]

type entries = Table.pre_entry list 

type vsets = Match.t list list 

type ctrl = entries * vsets

type loc = int [@@deriving sexp]

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
  | VRuntime of 
      { loc : loc;
        typ_name : string; }
  | VParser of vparser
  | VControl of vcontrol
  | VPackage of 
      { decl : Declaration.t;
        args : (string * value) list; }
  | VTable of vtable
  | VExternFun of 
      { name : string;
        caller : (loc * string) option; }
  [@@deriving sexp]

and vparser = {
  pvs : (string * value) list;
  pparams : Parameter.t list;
  plocals : Declaration.t list;
  states : Parser.state list;
}
[@@deriving sexp]

and vcontrol = {
  cvs : (string * value) list;
  cparams : Parameter.t list;
  clocals : Declaration.t list;
  apply : Block.t;
}
[@@deriving sexp]

and vtable = {
  name : string;
  keys : value list;
  actions : Table.action_ref list;
  default_action : Table.action_ref;
  const_entries : (set * Table.action_ref) list;
}
[@@deriving sexp]

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
[@@deriving sexp]

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
[@@deriving sexp]

and signal =
  | SContinue
  | SReturn of value
  | SExit
  | SReject of string
[@@deriving sexp]

val assert_bool : value -> bool 

val assert_rawint : value -> Bigint.t 

val assert_bit : value -> Bigint.t * Bigint.t 

val assert_int : value -> Bigint.t * Bigint.t 

val assert_varbit : value -> Bigint.t * Bigint.t * Bigint.t 

val assert_string : value -> string 

val assert_tuple : value -> value list 

val assert_set : value -> Bigint.t -> set 

val assert_error : value -> string 

val assert_fun : value -> Parameter.t list * Block.t

val assert_builtin : value -> string * lvalue 

val assert_action : value -> Parameter.t list * Block.t 

val assert_struct : value -> string * (string * value) list 

val assert_header : value -> string * (string * value) list * bool 

val assert_union : value -> string * value * (string * bool) list 

val assert_stack : value -> string * value list * Bigint.t * Bigint.t 

val assert_enum : value -> string * string 

val assert_senum : value -> string * string * value 

val assert_runtime : value -> int

val assert_parser : value -> vparser

val assert_control : value -> vcontrol 

val assert_package : value -> Declaration.t * (string * value) list 

val assert_table : value -> vtable 

val assert_lname : lvalue -> string 

val assert_ltopname : lvalue -> string 

val assert_lmember : lvalue -> lvalue * string 

val assert_lbitaccess : lvalue -> lvalue * Expression.t * Expression.t 

val assert_larrayaccess : lvalue -> lvalue * Expression.t 

val assert_singleton : set -> Bigint.t * Bigint.t 

val assert_mask : set -> value * value 

val assert_range : set -> value * value 

val assert_prod : set -> set list 

val assert_lpm : set -> value * Bigint.t * value 

val assert_valueset : set -> value * Match.t list list * set list
