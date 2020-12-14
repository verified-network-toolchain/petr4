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
  env -> 'st -> Type.t list -> (value * Type.t) list ->
  env * 'st * signal * value

type 'st apply =
  ctrl -> env -> 'st -> signal -> value -> Expression.t option list -> 'st * signal * value

module State = struct

  type 'a t = {
    externs : (string * 'a) list;
    heap : (string * value) list;
    packet : pkt;
  }

  let empty = {
    externs = [];
    heap = [];
    packet = {emitted = Cstruct.empty; main = Cstruct.empty; in_size = 0; }
  }

  let packet_location = "__PACKET__"

  let counter = ref 0

  let fresh_loc = fun () ->
    counter := !counter + 1;
    "__fresh_loc__" ^ (string_of_int (!counter)) ^ "__fresh_loc__"

  let reset_state st = counter := 0; { st with 
    packet = {emitted = Cstruct.empty; main = Cstruct.empty; in_size = 0; };
    heap = List.filter st.heap ~f:(fun (x,_) -> String.is_prefix x ~prefix:"__fresh_loc__");
  }

  let get_packet st = st.packet

  let set_packet pkt st = { st with packet = pkt }

  let insert_extern loc v st = {
    st with externs = (loc,v) :: st.externs }
  
  let find_extern loc st =
    let x = List.Assoc.find_exn st.externs loc ~equal:String.equal in
    x

  let insert_heap loc v st = { st with heap = (loc,v) :: st.heap }

  let find_heap loc st =
    List.Assoc.find_exn st.heap loc ~equal:String.equal

  let is_initialized loc st =
    List.exists st.externs ~f:(fun (x,_) -> String.equal x loc)

end

type 'a writer = bool -> (string * value) list -> string -> value -> value

type 'a reader = bool -> (string * value) list -> string -> value

let rec width_of_typ (env : env) (t : Type.t) : Bigint.t =
  match t with
  | Bool -> Bigint.one
  | Int {width} | Bit {width} -> Bigint.of_int width
  | Array {typ;size} -> Bigint.(width_of_typ env typ * of_int size)
  | List {types}
  | Tuple {types} ->
    types
    |> List.map ~f:(width_of_typ env)
    |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | Record rt | Header rt | Struct rt ->
    rt.fields
    |> List.map ~f:(fun x -> x.typ)
    |> List.map ~f:(width_of_typ env)
    |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | Enum {typ = Some t;_} -> width_of_typ env t
  | TypeName n -> width_of_typ env (EvalEnv.find_typ n env)
  | NewType nt -> width_of_typ env nt.typ
  | _ -> raise_s [%message "not a fixed-width type" ~t:(t:Type.t)]

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
  | HeaderUnion rt     -> init_val_of_union env rt
  | Struct rt          -> init_val_of_struct env rt
  | Enum et            -> init_val_of_enum env et
  | SpecializedType s  -> init_val_of_specialized s
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
  let vs = List.map tup.types ~f:(fun t -> init_val_of_typ env t) in
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

and init_val_of_union (env: env) (rt : RecordType.t) : value =
  let fs = List.map rt.fields ~f:(fun f -> f.name, init_val_of_typ env f.typ) in
  VUnion { fields = fs }

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
    let v = init_val_of_typ env t in
    VSenumField {
      typ_name = et.name;
      enum_name = List.hd_exn et.members;
      v;
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

let rec width_of_val v =
  let field_width (name, value) =
    width_of_val value
  in
  match v with
  | VBit {w;_}
  | VInt {w;_}
  | VVarbit{w;_} ->
      w
  | VNull ->
      Bigint.zero
  | VBool _ ->
      Bigint.one
  | VStruct {fields}
  | VHeader {fields; _} ->
      fields
      |> List.map ~f:field_width
      |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | VSenumField {v; _} ->
      width_of_val v
  | VInteger _ -> failwith "width of VInteger"
  | VUnion _ -> failwith "width of header union unimplemented"
  | _ -> raise_s [%message "width of type unimplemented" ~v:(v: Value.value)]

let rec value_of_lvalue (reader : 'a reader) (env : env) (st : 'a State.t)
    (lv : lvalue) : signal * value =
  match lv.lvalue with
  | LName{name=n}                     -> SContinue, State.find_heap (EvalEnv.find_val n env) st
  | LMember{expr=lv;name=n}           -> value_of_lmember reader st env lv n
  | LBitAccess{expr=lv;msb=hi;lsb=lo} -> value_of_lbit reader st env lv hi lo
  | LArrayAccess{expr=lv;idx}         -> value_of_larray reader st env lv idx

and value_of_lmember (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (n : string) : signal * value =
  let (s,v) = value_of_lvalue reader env st lv in
  let v' = match v with
    | VHeader{fields=l;is_valid} -> reader is_valid l n 
    | VStruct{fields=l;_}
    | VUnion{fields=l;_} -> find_exn l n
    | VStack{headers=vs;size=s;next=i;_} -> value_of_stack_mem_lvalue st n vs s i
    | _ -> failwith "no lvalue member" in
  match s with
  | SContinue -> (s,v')
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_lbit (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (hi : Bigint.t) (lo : Bigint.t) : signal * value =
  let (s,n) = value_of_lvalue reader env st lv in
  let n' = n |> bigint_of_val in
  match s with 
  | SContinue -> s, VBit{w=Bigint.(hi - lo + one);v=bitstring_slice n' hi lo}
  | SReject _ | SReturn _ | SExit -> s, VNull

and value_of_larray (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (idx : Bigint.t) : signal * value =
  let (s,v) = value_of_lvalue reader env st lv in
  match s with
  | SContinue ->
    begin match v with
      | VStack{headers=vs;size=s;next=i} ->
        begin try (SContinue, List.nth_exn vs Bigint.(to_int_exn (idx % s)))
          with Invalid_argument _ -> (SReject "StackOutOfBounds", VNull) end
      | _ -> failwith "array access is not a header stack" end
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_stack_mem_lvalue (st : 'a State.t) (name : string) (ls : value list)
(size : Bigint.t) (next : Bigint.t) : value =
  match name with
  | "next" -> List.nth_exn ls Bigint.(to_int_exn (next % size))
  | _ -> failwith "not an lvalue"

let rec assign_lvalue (reader : 'a reader) (writer : 'a writer) (st : 'a State.t) 
    (env : env) (lhs : lvalue) (rhs : value) : 'a State.t * signal =
  match lhs.lvalue with
  | LName {name} ->
    let l = EvalEnv.find_val name env in
    State.insert_heap l rhs st, SContinue
  | LMember{expr=lv;name=mname;} ->
    let signal1, record = value_of_lvalue reader env st lv in
    let rhs', signal2 = update_member writer record mname rhs in
    let inc_next = String.equal mname "next" in
    let rhs' = match rhs' with
      | VStack{headers; size; next} -> Bigint.(VStack {headers; size; next = next + (if inc_next then one else zero)})
      | _ -> rhs' in
    begin match signal1, signal2 with
      | SContinue, SContinue ->
        assign_lvalue reader writer st env lv rhs'
      | SContinue, _ -> st, signal2
      | _, _ -> st, signal1
    end
  | LBitAccess{expr=lv;msb;lsb;} ->
    let signal, bits = value_of_lvalue reader env st lv in
    begin match signal with
      | SContinue -> 
        assign_lvalue reader writer st env lv (update_slice bits msb lsb rhs)
      | _ -> st, signal
    end
  | LArrayAccess{expr=lv;idx;} ->
    let signal1, arr = value_of_lvalue reader env st lv in
    let rhs', signal2 = update_idx arr idx rhs in
    begin match signal1, signal2 with
      | SContinue, SContinue -> 
        assign_lvalue reader writer st env lv rhs'
      | SContinue, _ -> st, signal2
      | _, _ -> st, signal1  
    end

and update_member (writer : 'a writer) (value : value) (fname : string)
    (fvalue : value) : value * signal =
  match value with
  | VStruct v ->
    update_field v.fields fname fvalue, SContinue
  | VHeader v -> writer v.is_valid v.fields fname fvalue, SContinue
  | VUnion {fields} ->
    update_union_member fields fname fvalue
  | VStack{headers=hdrs; size=s; next=i} ->
    let idx = 
      match fname with
      | "next" -> i
      | "last" -> Bigint.(i - one)
      | _ -> failwith "BUG: VStack has no such member"
    in
    update_idx value idx fvalue
  | _ -> failwith "member access undefined"

and update_union_member (fields : (string * value) list)
    (member_name : string) (new_value : value) : value * signal =
  let new_fields, new_value_valid = assert_header new_value in
  let set_validity value validity =
    let value_fields, _ = assert_header value in
    VHeader {fields = value_fields; is_valid = validity}
  in
  let update_field (name, value) =
    if new_value_valid
    then if name = member_name
         then name, new_value
         else name, set_validity value false
    else name, set_validity value false
  in
  VUnion {fields = List.map ~f:update_field fields}, SContinue

and update_field (fields : (string * value) list) (field_name : string)
    (field_value : value) : value =
  let update (n, v) =
    if String.equal n field_name
    then n, field_value
    else n, v in
  VStruct {fields = List.map fields ~f:update}

and update_nth (l : value list) (n : Bigint.t)
    (x : value) : value list =
  let n = Bigint.to_int_exn n in
  let xs, ys = List.split_n l n in
  match ys with
  | y :: ys -> xs @ x :: ys
  | [] -> failwith "update_nth: out of bounds"

and update_idx (arr : value) (idx : Bigint.t)
    (value : value) : value * signal =
  match arr with
  | VStack{headers; size; next} ->
     if Bigint.(idx < zero || idx >= size)
     then VNull, SReject "StackOutOfBounds"
     else VStack {headers = update_nth headers idx value; next; size}, SContinue
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

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern : 
    string -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> state -> state

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> state * env * pkt option

  val get_outport : state -> env -> Bigint.t

end
