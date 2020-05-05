module I = Info
open Typed
open Prog
open Value
open Env
open Bitstring
open Core_kernel
open Util
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

type env = EvalEnv.t

type 'st pre_extern =
  ctrl -> env -> 'st -> Type.t list -> (value * Type.t) list ->
  env * 'st * signal * value

type 'st apply =
  ctrl -> env -> 'st -> signal -> value -> Expression.t option list -> env * 'st * signal * value

let rec init_val_of_typ (env : env) (typ : Type.t) : value =
  match typ with
  | Bool               -> VBool false
  | String             -> VString ""
  | Integer            -> VInteger Bigint.zero
  | Int w              -> VInt{w=Bigint.of_int w.width; v=Bigint.zero}
  | Bit w              -> VBit{w=Bigint.of_int w.width; v=Bigint.zero}
  | VarBit w           -> VVarbit{max=Bigint.of_int w.width; w=Bigint.zero; v=Bigint.zero}
  | Array arr          -> init_val_of_array env arr
  | Tuple tup          -> init_val_of_tuple env tup
  | List l             -> init_val_of_tuple env l
  | Record r           -> init_val_of_record env r
  | Set s              -> VSet SUniversal
  | Error              -> VError "NoError"
  | MatchKind          -> VMatchKind "exact"
  | TypeName name      -> init_val_of_typname env name
  | NewType nt         -> init_val_of_newtyp env nt
  | Void               -> VNull
  | Header rt          -> init_val_of_header env rt
  | HeaderUnion rt     -> init_val_of_union rt
  | Struct rt          -> init_val_of_struct env rt
  | Enum et            -> init_val_of_enum env et
  | SpecializedType st -> init_val_of_specialized st
  | Package pt         -> init_val_of_pkg pt
  | Control ct         -> init_val_of_ctrl ct
  | Parser pt          -> init_val_of_prsr pt
  | Extern et          -> init_val_of_ext et
  | Function ft        -> init_val_of_func ft
  | Action at          -> init_val_of_act at
  | Constructor ct     -> init_val_of_constr ct
  | Table tt           -> init_val_of_table tt

and init_val_of_array (env : env) (arr : ArrayType.t) : value =
  let hdrs =
    arr.size
    |> List.init ~f:string_of_int
    |> List.map ~f:(fun _ -> init_val_of_typ env arr.typ) in
  VStack {
    headers = hdrs;
    size = arr.size |> Bigint.of_int;
    next = Bigint.zero;
  }

and init_val_of_tuple (env : env) (tup : TupleType.t) : value =
  let vs = List.map tup.types ~f:(init_val_of_typ env) in
  VTuple vs

and init_val_of_record (env : env) (r : RecordType.t) : value =
  let vs = List.map r.fields ~f:(fun f -> f.name, init_val_of_typ env f.typ) in
  VRecord vs

and init_val_of_typname (env : env) (tname : Types.name) : value =
  init_val_of_typ env (EvalEnv.find_typ tname env)

and init_val_of_newtyp (env : env) (nt : NewType.t) : value = 
  init_val_of_typ env nt.typ

and init_val_of_header (env : env) (rt : RecordType.t) : value =
  let fs = List.map rt.fields ~f:(fun f -> f.name, init_val_of_typ env f.typ) in
  VHeader {
    fields = fs;
    is_valid = false
  }

and init_val_of_union (rt : RecordType.t) : value =
  let bs = List.map rt.fields ~f:(fun f -> f.name, false) in
  VUnion {
    valid_header = VNull;
    valid_fields = bs;
  }

and init_val_of_struct (env : env) (rt : RecordType.t) : value =
  let fs = List.map rt.fields ~f:(fun f -> f.name, init_val_of_typ env f.typ) in
  VStruct {
    fields = fs;
  }

and init_val_of_enum (env : env) (et : EnumType.t) : value =
  match et.typ with
  | None ->
    VEnumField {
      typ_name = et.name;
      enum_name = List.hd_exn et.members
    }
  | Some t ->
    VSenumField {
      typ_name = et.name;
      enum_name = List.hd_exn et.members;
      v = init_val_of_typ env t;
    }

and init_val_of_specialized (st : SpecializedType.t) : value =
  failwith "init vals unimplemented for specialized types"

and init_val_of_pkg (pt : PackageType.t) : value =
  failwith "init vals unimplemented for package types"

and init_val_of_ctrl (ct : ControlType.t) : value =
  failwith "init vals unimplemented for control types"

and init_val_of_prsr (pt : ControlType.t) : value =
  failwith "init vals unimplemented for parser types"

and init_val_of_ext (et : ExternType.t) : value =
  failwith "init vals unimplemented for extern types"

and init_val_of_func (ft : FunctionType.t) : value =
  failwith "init vals unimplemented for function types"

and init_val_of_act (at : ActionType.t) : value =
  failwith "init vals unimplemented for action types"

and init_val_of_constr (ct : ConstructorType.t) : value =
  failwith "init vals unimplemented for constructor types"

and init_val_of_table (tt : TableType.t) : value =
  failwith "init vals unimplemented for table  types"

let rec implicit_cast_from_rawint (env : env) (v : value) (t : Type.t) : value =
  match v with
  | VInteger n ->
    begin match t with
      | Int {width} -> int_of_rawint n (Bigint.of_int width)
      | Bit {width} -> bit_of_rawint n (Bigint.of_int width)
      | TypeName n -> implicit_cast_from_rawint env v (EvalEnv.find_typ n env)
      | _ -> v
      end
  | _ -> v

let rec implicit_cast_from_tuple (env : env) (v : value) (t : Type.t) : value =
  match v with
  | VTuple l ->
    begin match t with
      | Struct rt -> 
        rt.fields
        |> fun x -> List.zip_exn x l
        |> List.map ~f:(fun (f,v : RecordType.field * value) -> f, implicit_cast_from_tuple env v f.typ)
        |> List.map ~f:(fun (f,v : RecordType.field * value) -> f.name, implicit_cast_from_rawint env v f.typ)
        |> fun fields -> VStruct {fields}
      | Header rt ->
        rt.fields
        |> fun x -> List.zip_exn x l
        |> List.map ~f:(fun (f,v : RecordType.field * value) -> f, implicit_cast_from_tuple env v f.typ)
        |> List.map ~f:(fun (f,v : RecordType.field * value) -> f.name, implicit_cast_from_rawint env v f.typ)
        |> fun fields -> VHeader {fields; is_valid = true}
      | TypeName n -> implicit_cast_from_tuple env v (EvalEnv.find_typ n env)
      | _ -> VTuple l end
  | VRecord r -> failwith "TODO"
  | _ -> v

let rec value_of_lvalue (env : env) (lv : lvalue) : signal * value =
  match lv.lvalue with
  | LName{name=n}                     -> SContinue, EvalEnv.find_val n env
  | LMember{expr=lv;name=n}           -> value_of_lmember env lv n
  | LBitAccess{expr=lv;msb=hi;lsb=lo} -> value_of_lbit env lv hi lo
  | LArrayAccess{expr=lv;idx}         -> value_of_larray env lv idx

and value_of_lmember (env : env) (lv : lvalue) (n : string) : signal * value =
  let (s,v) = value_of_lvalue env lv in
  let v' = match v with
    | VStruct{fields=l;_}
    | VHeader{fields=l;_}              ->
      find_exn l n
    | VUnion{valid_header=v;_}         -> v
    | VStack{headers=vs;size=s;next=i;_} -> value_of_stack_mem_lvalue n vs s i
    | _ -> failwith "no lvalue member" in
  match s with
  | SContinue -> (s,v')
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_lbit (env : env) (lv : lvalue) (hi : Bigint.t)
    (lo : Bigint.t) : signal * value =
  let (s,n) = value_of_lvalue env lv in
  let n' = bigint_of_val n in
  match s with
  | SContinue -> (s, VBit{w=Bigint.(hi - lo + one);v=bitstring_slice n' hi lo})
  | SReject _ -> (s, VNull)
  | _ -> failwith "unreachable"

and value_of_larray (env : env) (lv : lvalue)
    (idx : value) : signal * value =
  let (s,v) =  value_of_lvalue env lv in
  match s with
  | SContinue ->
    begin match v with
      | VStack{headers=vs;size=s;next=i} ->
        let idx' = bigint_of_val idx in
        begin try (SContinue, List.nth_exn vs Bigint.(to_int_exn (idx' % s)))
          with Invalid_argument _ -> (SReject "StackOutOfBounds", VNull) end
      | _ -> failwith "array access is not a header stack" end
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_stack_mem_lvalue (name : string) (vs : value list)
(size : Bigint.t) (next : Bigint.t) : value =
  match name with
  | "next" -> List.nth_exn vs Bigint.(to_int_exn (next % size))
  | _ -> failwith "not an lvalue"


let rec assign_lvalue (env: env) (lhs : lvalue) (rhs : value) : env * signal =
  let rhs = 
    match rhs with
    | VTuple l -> implicit_cast_from_tuple env rhs lhs.typ
    | VInteger n -> implicit_cast_from_rawint env rhs lhs.typ
    | _ -> rhs
  in
  match lhs.lvalue with
  | LName {name} ->
     EvalEnv.insert_val name rhs env, SContinue
  | LMember{expr=lv;name=mname;} ->
     let _, record = value_of_lvalue env lv in
     assign_lvalue env  lv (update_member record mname rhs)
  | LBitAccess{expr=lv;msb;lsb;} ->
     let _, bits = value_of_lvalue env lv in
     assign_lvalue env lv (update_slice bits msb lsb rhs)
  | LArrayAccess{expr=lv;idx;} ->
     let _, arr = value_of_lvalue env lv in
     let idx = bigint_of_val idx in
     assign_lvalue env  lv (update_idx arr idx rhs)

and update_member (value : value) (fname : string) (fvalue : value) : value =
  match value with
  | VStruct v ->
     VStruct {fields=update_field v.fields fname fvalue}
  | VHeader v ->
     VHeader {fields=update_field v.fields fname fvalue;
              is_valid=true}
  | VUnion v ->
     VUnion {valid_header=fvalue;
             valid_fields=set_only_valid v.valid_fields fname}
  | VStack{headers=hdrs; size=s; next=i} ->
     let idx = 
       match fname with
       | "next" -> i
       | "last" -> Bigint.(i - one)
       | _ -> failwith "BUG: VStack has no such member"
     in
     update_idx value idx fvalue
  | _ -> failwith "member access undefined"

and set_only_valid fields (fname: string) =
  List.map fields ~f:(fun (name, _) -> name, name = fname)

and update_field fields field_name field_value =
  List.map fields ~f:(fun (name, old_value) ->
      if name = field_name
      then (name, field_value)
      else (name, old_value))

and update_nth l n x =
  let n = Bigint.to_int_exn n in
  let xs, ys = List.split_n l n in
  match ys with
  | y :: ys -> xs @ x :: ys
  | [] -> failwith "update_nth: out of bounds"

and update_idx arr idx value =
  match arr with
  | VStack{headers; size; next} ->
     if Bigint.(idx < zero || idx >= size)
     then failwith "out-of-bounds array access"
     else VStack { headers = update_nth headers idx value;
                   size = size;
                   next = next }
  | _ -> failwith "BUG: update_idx: expected a stack"

and update_slice bits_val msb lsb rhs_val =
  let open Bigint in
  let width =
    match bits_val with
    | VBit { w; _ } -> w
    | _ -> failwith "BUG:expected bit<> type"
  in
  let bits = bigint_of_val bits_val in
  let rhs_shifted = bigint_of_val rhs_val lsl to_int_exn lsb in
  let mask = lnot ((power_of_two (msb + one) - one)
                   lxor (power_of_two lsb - one))
  in
  let new_bits = (bits land mask) lxor rhs_shifted in
  VBit { w = width; v = new_bits }

module State = struct

  type 'a t = (string * 'a) list

  let packet_location = "_PACKET_"

  let empty = []

  let insert loc v st = (loc, v) :: st
  
  let find loc st =
    List.Assoc.find_exn (* TODO *) st loc ~equal:String.equal

  let filter ~f st =
    List.filter ~f st

  let map ~f st =
    let go (loc, x) = (loc, f x) in
    List.map ~f:go st

  let merge s1 s2 =
    s1 @ s2

  let is_initialized loc st = List.exists st ~f:(fun (x,_) -> String.equal x loc)

end

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val eval_extern : 
    string -> ctrl -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> state * env * pkt

end
