open Types
open Sexplib.Conv

type buf = Cstruct_sexp.t [@@deriving sexp]
let buf_to_yojson b = failwith "unimplemented"
let buf_of_yojson j = failwith "unimplemented"

type packet_in = buf [@@deriving sexp,yojson]
type packet_out = buf * buf [@@deriving sexp,yojson]

type entries = Table.pre_entry list

type value_sets = Match.t list list

type ctrl = entries * value_sets

type value =
  | VNull
  | VBool of bool
  | VInteger of Util.bigint
  | VBit of 
      { w : Util.bigint;
        v : Util.bigint; }
  | VInt of 
      { w : Util.bigint;
        v : Util.bigint; }
  | VVarbit of 
      { max : Util.bigint;
        w : Util.bigint;
        v : Util.bigint; }
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
      { fields : (string * value) list; }
  | VHeader of 
      { fields : (string * value) list;
        is_valid : bool }
  | VUnion of 
      { valid_header : value;
        valid_fields : (string * bool) list; }
  | VStack of 
      { headers : value list;
        size : Util.bigint;
        next : Util.bigint; }
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
[@@deriving sexp,yojson]

and vparser = {
  pvs : (string * value) list;
  pparams : Parameter.t list;
  plocals : Declaration.t list;
  states : Parser.state list;
}
[@@deriving sexp,yojson]

and vcontrol = {
  cvs : (string * value) list;
  cparams : Parameter.t list;
  clocals : Declaration.t list;
  apply : Block.t;
}
[@@deriving sexp,yojson]

and vtable = {
  name : string;
  keys : value list;
  actions : Table.action_ref list;
  default_action : Table.action_ref;
  const_entries : (set * Table.action_ref) list;
}
[@@deriving sexp,yojson]

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
[@@deriving sexp,yojson]

and set =
  | SSingleton of 
      { w : Util.bigint;
        v : Util.bigint; }
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
        nbits : Util.bigint;
        v : value; }
  | SValueSet of 
      { size : value;
        members : Match.t list list;
        sets : set list; }
[@@deriving sexp,yojson]

and signal =
  | SContinue
  | SReturn of value
  | SExit
  | SReject of string
[@@deriving sexp,yojson]

and vruntime =
  | PacketIn of packet_in
  | PacketOut of packet_out
[@@deriving sexp,yojson]

let assert_bool v =
  match v with 
  | VBool b -> b 
  | _ -> failwith "not a bool"

let assert_rawint v = 
  match v with 
  | VInteger n -> n 
  | _ -> failwith "not an variable-size integer"

let assert_bit v = 
  match v with 
  | VBit{w;v} -> (w,v) 
  | _ -> failwith "not a bitstring"

let assert_int v = 
  match v with 
  | VInt {w;v} -> (w,v)
  | _ -> failwith "not an int"

let assert_varbit v = 
  match v with 
  | VVarbit {max;w;v} -> (max,w,v) 
  | _ -> failwith "not a varbit"

let assert_string v = 
  match v with 
  | VString s -> s
  | _ -> failwith "not a string"

let assert_tuple v = 
  match v with 
  | VTuple l -> l 
  | _ -> failwith "not a tuple"

let assert_set v w = 
  match v with
  | VSet s -> s 
  | VInteger i -> SSingleton{w;v=i}
  | VInt {v=i;_} -> SSingleton{w;v=i}
  | VBit{v=i;_} -> SSingleton{w;v=i}
  | _ -> failwith "not a set"

let assert_error v =
  match v with 
  | VError s -> s
  | _ -> failwith "not an error"

let assert_fun v =
  match v with 
  | VFun {params;body} -> (params,body)
  | _ -> failwith "not a function"

let assert_builtin v =
  match v with 
  | VBuiltinFun {name; caller} -> name, caller
  | _ -> failwith "not a builtin function"

let assert_action v = 
  match v with 
  | VAction {params;body} -> (params, body)
  | _ -> failwith "not an action"

let assert_struct v =
  match v with 
  | VStruct {fields} -> fields
  | _ -> failwith "not a struct"

let assert_header v = 
  match v with 
  | VHeader {fields;is_valid} -> (fields, is_valid)
  | _ -> failwith "not a header"

let assert_union v = 
  match v with 
  | VUnion {valid_header;valid_fields} -> (valid_header, valid_fields)
  | _ -> failwith "not a union"

let assert_stack v = 
  match v with 
  | VStack {headers;size;next} -> (headers, size, next)
  | _ -> failwith "not a stack"

let assert_enum v = 
  match v with 
  | VEnumField {typ_name;enum_name} -> (typ_name, enum_name)
  | _ -> failwith "not an enum field"

let assert_senum v = 
  match v with 
  | VSenumField {typ_name;enum_name;v} -> (typ_name, enum_name, v)
  | _ -> failwith "not an senum field"

let assert_runtime v = 
  match v with 
  | VRuntime r -> r 
  | _ -> failwith "not a runtime value"

let assert_parser v = 
  match v with 
  | VParser p -> p 
  | _ -> failwith "not a parser"

let assert_control v = 
  match v with 
  | VControl c -> c 
  | _ -> failwith "not a control"

let assert_package v = 
  match v with 
  | VPackage {decl;args} -> (decl, args) 
  | _ -> failwith "not a package"

let assert_table v = 
  match v with 
  | VTable t -> t 
  | _ -> failwith "not a table"

let assert_lname l = 
  match l with 
  | LName s -> s 
  | _ -> failwith "not an lvalue name"

let assert_ltopname l = 
  match l with 
  | LTopName s -> s 
  | _ -> failwith "not an lvalue top-leval name "

let assert_lmember l =
  match l with 
  | LMember {expr; name} -> (expr, name) 
  | _ -> failwith "not an lvalue member"

let assert_lbitaccess l = 
  match l with 
  | LBitAccess {expr; msb; lsb} -> (expr, msb, lsb)
  | _ -> failwith "not an lvalue bitaccess"

let assert_larrayaccess l = 
  match l with 
  | LArrayAccess {expr; idx} -> (expr, idx)
  | _ -> failwith "not an lvalue array access"

let assert_singleton s = 
  match s with 
  | SSingleton {w; v} -> (w,v) 
  | _ -> failwith "not a singleton set"

let assert_mask s = 
  match s with 
  | SMask {v;mask} -> (v,mask) 
  | _ -> failwith "not a mask set"

let assert_range s = 
  match s with 
  | SRange{lo;hi} -> (lo,hi)
  | _ -> failwith "not a range set"

let assert_prod s = 
  match s with 
  | SProd l -> l
  | _ -> failwith "not a product set"

let assert_lpm s = 
  match s with 
  | SLpm {w; nbits; v} -> (w,nbits,v) 
  | _ -> failwith "not an lpm set"

let assert_valueset s = 
  match s with 
  | SValueSet {size; members; sets} -> (size, members, sets)
  | _ -> failwith "not a valueset"

let assert_packet_in r = 
  match r with 
  | PacketIn p -> p
  | _ -> failwith "not a packet in"

let assert_packet_out r = 
  match r with 
  | PacketOut p -> p 
  | _ -> failwith "not a packet out"
