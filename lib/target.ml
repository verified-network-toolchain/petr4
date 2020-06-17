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
    "_" ^ (string_of_int (!counter)) ^ "_" 

  let get_packet st = st.packet

  let set_packet pkt st = { st with packet = pkt }

  let insert_extern loc v st = {
    st with externs = (loc,v) :: st.externs }
  
  let find_extern loc st =
    let x = List.Assoc.find_exn st.externs loc ~equal:String.equal in
    x

  let insert_heap loc v st = 
    print_endline "inserting into the heap";
    print_endline (Sexp.to_string (sexp_of_value v));
    print_endline "with location";
    print_endline loc;
    {
    st with heap = (loc,v) :: st.heap}

  let find_heap loc st = 
    (* print_endline "probably about to fail"; *)
    let x = List.Assoc.find_exn st.heap loc ~equal:String.equal in
    (* print_endline "didn't actually fail"; *)
    x

  let is_initialized loc st =
    List.exists st.externs ~f:(fun (x,_) -> String.equal x loc)

end

type 'a writer = 'a State.t -> bool -> (string * loc) list -> string -> value -> 'a State.t

type 'a reader = 'a State.t -> bool -> (string * loc) list -> string -> value

let rec extract_from_state (st : 'a State.t) (v : value) : value =
  match v with
  | VLoc l -> extract_from_state st (State.find_heap l st)
  | _ -> v

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

let rec init_val_of_typ (st : 'a State.t) (env : env) (typ : Type.t) : 'a State.t * value =
  match typ with
  | Bool               -> st, (VBool false)
  | String             -> st, (VString "")
  | Integer            -> st, (VInteger Bigint.zero)
  | Int w              -> st, (VInt{w=Bigint.of_int w.width; v=Bigint.zero})
  | Bit w              -> st, (VBit{w=Bigint.of_int w.width; v=Bigint.zero})
  | VarBit w           -> st, (VVarbit{max=Bigint.of_int w.width; w=Bigint.zero; v=Bigint.zero})
  | Array arr          -> (init_val_of_array st env arr)
  | Tuple tup          -> (init_val_of_tuple st env tup)
  | List l             -> (init_val_of_tuple st env l)
  | Record r           -> (init_val_of_record st env r)
  | Set s              -> st, (VSet SUniversal)
  | Error              -> st, (VError "NoError")
  | MatchKind          -> st, (VMatchKind "exact")
  | TypeName name      -> init_val_of_typname st env name
  | NewType nt         -> init_val_of_newtyp st env nt
  | Void               -> st, VNull
  | Header rt          -> (init_val_of_header st env rt)
  | HeaderUnion rt     -> (init_val_of_union st env rt)
  | Struct rt          -> (init_val_of_struct st env rt)
  | Enum et            -> (init_val_of_enum st env et)
  | SpecializedType s  -> st, init_val_of_specialized s
  | Package pt         -> st, init_val_of_pkg pt
  | Control ct         -> st, init_val_of_ctrl ct
  | Parser pt          -> st, init_val_of_prsr pt
  | Extern et          -> st, init_val_of_ext et
  | Function ft        -> st, init_val_of_func ft
  | Action at          -> st, init_val_of_act at
  | Constructor ct     -> st, init_val_of_constr ct
  | Table tt           -> st, init_val_of_table tt

and init_val_of_array (st : 'a State.t) (env : env)
    (arr : ArrayType.t) : 'a State.t * value =
  let (st, hdrs) =
    arr.size
    |> List.init ~f:string_of_int
    |> List.fold_map ~init: st ~f:(fun st _ -> init_val_of_typ st env arr.typ) in
  let ls = List.map hdrs ~f:(fun x -> State.fresh_loc ()) in
  let st = List.fold2_exn ls hdrs ~init:st ~f:(fun acc l v -> State.insert_heap l v acc) in
  st, VStack {
    headers = ls;
    size = arr.size |> Bigint.of_int;
    next = Bigint.zero;
  }

and init_val_of_tuple (st : 'a State.t) (env : env)
    (tup : TupleType.t) : 'a State.t * value =
  let (st, vs) = List.fold_map ~init:st tup.types
    ~f:(fun st t -> init_val_of_typ st env t) in
  st, VTuple vs

and init_val_of_record (st : 'a State.t) (env : env)
    (r : RecordType.t) : 'a State.t * value =
  let (st, vs) = List.fold_map r.fields ~init:st
    ~f:(fun st f -> let st, v = init_val_of_typ st env f.typ in st, (f.name, v)) in
  st, VRecord vs

and init_val_of_typname (st : 'a State.t) (env : env)
    (tname : Types.name) : 'a State.t * value =
  init_val_of_typ st env (EvalEnv.find_typ tname env)

and init_val_of_newtyp (st : 'a State.t) (env : env)
    (nt : NewType.t) : 'a State.t * value = 
  init_val_of_typ st env nt.typ

and init_val_of_header (st : 'a State.t) (env : env)
    (rt : RecordType.t) : 'a State.t * value =
  let (st, fs) = List.fold_map rt.fields ~init:st
    ~f:(fun st f -> let st, v = init_val_of_typ st env f.typ in st, (f.name, v)) in
  let (ns, hs) = List.unzip fs in
  let ls = List.map hs ~f:(fun _ -> State.fresh_loc ()) in
  let st = List.fold2_exn ls hs ~init:st ~f:(fun acc l h -> State.insert_heap l h acc) in
  st, VHeader {
    fields = List.zip_exn ns ls;
    is_valid = false
  }

and init_val_of_union (st : 'a State.t) (env: env) (rt : RecordType.t) : 'a State.t * value =
  let st, fs = List.fold_map rt.fields ~init:st 
    ~f:(fun st f -> let st, v = init_val_of_typ st env f.typ in st, (f.name, v)) in
  let (ns, hs) = List.unzip fs in
  let ls = List.map hs ~f:(fun _ -> State.fresh_loc ()) in
  let st = List.fold2_exn ls hs ~init:st ~f:(fun acc l h -> State.insert_heap l h acc) in
  st, VUnion {
    fields = List.zip_exn ns ls;
  }

and init_val_of_struct (st : 'a State.t) (env : env) (rt : RecordType.t) : 'a State.t * value =
  let (st, fs) = List.fold_map rt.fields ~init:st
    ~f:(fun st f -> let st, v = init_val_of_typ st env f.typ in st, (f.name, v)) in
  let (ns, hs) = List.unzip fs in
  let ls = List.map hs ~f:(fun _ -> State.fresh_loc ()) in
  let st = List.fold2_exn ls hs ~init:st ~f:(fun acc l h -> State.insert_heap l h acc) in
  st, VStruct {
    fields = List.zip_exn ns ls;
  }

and init_val_of_enum (st : 'a State.t) (env : env) (et : EnumType.t) : 'a State.t * value =
  match et.typ with
  | None ->
    st, VEnumField {
      typ_name = et.name;
      enum_name = List.hd_exn et.members
    }
  | Some t ->
    let (st,v) = init_val_of_typ st env t in
    st, VSenumField {
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

let rec width_of_val st v =
  let field_width (name, value) =
    width_of_val st value
  in
  match v with
  | VLoc l -> width_of_val st (State.find_heap l st)
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
      |> List.map ~f:(fun (x, y) -> x, State.find_heap y st)
      |> List.map ~f:field_width
      |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | VSenumField {v; _} ->
      width_of_val st v
  | VInteger _ -> failwith "width of VInteger"
  | VUnion _ -> failwith "width of header union unimplemented"
  | _ -> raise_s [%message "width of type unimplemented" ~v:(v: Value.value)]

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

let rec implicit_cast_from_tuple (st : 'a State.t) (env : env) (v : value)
    (t : Type.t) : 'a State.t * value =
  match v with
  | VTuple l -> let open RecordType in
    begin match t with
      | Struct rt -> 
        let (st, vs) = rt.fields
          |> fun x -> List.zip_exn x l
          |> List.fold_map ~init:st 
            ~f:(fun st (f,v) -> let st, v = implicit_cast_from_tuple st env v f.typ in st, (f,v)) in
        let (ns, vs) = vs
          |> List.map ~f:(fun (f,v) -> f.name, implicit_cast_from_rawint env v f.typ)
          |> List.unzip in
        let ls = List.map vs ~f:(fun _ -> State.fresh_loc ()) in
        let st = List.fold2_exn ls vs ~init:st 
          ~f:(fun acc l v -> State.insert_heap l v acc) in
        st, VStruct {fields = List.zip_exn ns ls}
      | Header rt ->
        let (st, vs) = rt.fields
          |> fun x -> List.zip_exn x l
          |> List.fold_map ~init:st 
            ~f:(fun st (f,v) -> let st, v = implicit_cast_from_tuple st env v f.typ in st, (f, v)) in
        let (ns, vs) = vs
          |> List.map ~f:(fun (f,v) -> f.name, implicit_cast_from_rawint env v f.typ)
          |> List.unzip in
        let ls = List.map vs ~f:(fun _ -> State.fresh_loc ()) in
        let st = List.fold2_exn ls vs ~init:st 
          ~f:(fun acc l v -> State.insert_heap l v acc) in
        st, VHeader {fields = List.zip_exn ns ls; is_valid = true}
      | TypeName n -> implicit_cast_from_tuple st env v (EvalEnv.find_typ n env)
      | _ -> st, VTuple l end
  | VRecord r -> failwith "TODO"
  | _ -> st, v

let rec implicit_cast st env value tgt_typ =
  match value with
  | VTuple l -> implicit_cast_from_tuple st env value tgt_typ
  | VInteger n -> st, implicit_cast_from_rawint env value tgt_typ
  | VLoc l -> 
    let (st, v) = implicit_cast st env (State.find_heap l st) tgt_typ in
    State.insert_heap l v st, VLoc l
  | _ -> st, value

let rec value_of_lvalue (reader : 'a reader) (st : 'a State.t) (env : env) 
    (lv : lvalue) : signal * value =
  match lv.lvalue with
  | LName{name=n}                     -> SContinue, EvalEnv.find_val n env
  | LMember{expr=lv;name=n}           -> value_of_lmember reader st env lv n
  | LBitAccess{expr=lv;msb=hi;lsb=lo} -> value_of_lbit reader st env lv hi lo
  | LArrayAccess{expr=lv;idx}         -> value_of_larray reader st env lv idx

and value_of_lmember (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (n : string) : signal * value =
  let (s,v) = value_of_lvalue reader st env lv in
  let v' = match v with
    | VHeader{fields=l;is_valid} -> reader st is_valid l n 
    | VStruct{fields=l;_}
    | VUnion{fields=l;_} ->
      print_endline "only other option in target";
      let x = State.find_heap (find_exn l n) st in
      print_endline "also a bust";
      x
    | VStack{headers=vs;size=s;next=i;_} -> value_of_stack_mem_lvalue st n vs s i
    | _ -> failwith "no lvalue member" in
  match s with
  | SContinue -> (s,v')
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_lbit (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (hi : Bigint.t) (lo : Bigint.t) : signal * value =
  let (s,n) = value_of_lvalue reader st env lv in
  let n' = n |> bigint_of_val in
  match s with 
  | SContinue -> s, VBit{w=Bigint.(hi - lo + one);v=bitstring_slice n' hi lo}
  | SReject _ | SReturn _ | SExit -> s, VNull

and value_of_larray (reader : 'a reader) (st : 'a State.t) (env : env) (lv : lvalue)
    (idx : value) : signal * value =
  let (s,v) = value_of_lvalue reader st env lv in
  match s with
  | SContinue ->
    begin match v with
      | VStack{headers=vs;size=s;next=i} ->
        let idx' = bigint_of_val idx in
        begin try (SContinue, State.find_heap (List.nth_exn vs Bigint.(to_int_exn (idx' % s))) st)
          with Invalid_argument _ -> (SReject "StackOutOfBounds", VNull) end
      | _ -> failwith "array access is not a header stack" end
  | SReject _ -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_stack_mem_lvalue (st : 'a State.t) (name : string) (ls : loc list)
(size : Bigint.t) (next : Bigint.t) : value =
  match name with
  | "next" -> State.find_heap (List.nth_exn ls Bigint.(to_int_exn (next % size))) st
  | _ -> failwith "not an lvalue"

let rec assign_lvalue (reader : 'a reader) (writer : 'a writer) (st : 'a State.t) 
    (env : env) (lhs : lvalue) (rhs : value)
    (inc_next : bool) : 'a State.t * env * signal =
  let st, rhs = implicit_cast st env rhs lhs.typ in
  match lhs.lvalue with
  | LName {name} ->
    let v = EvalEnv.find_val name env in
    begin match v with 
      | VLoc l ->
        print_endline "assigning to name by inserting into heap";
        print_endline ("the name is " ^ Types.name_only name);
        State.insert_heap l rhs st, env, SContinue
      | _ -> begin match (print_endline "call to update val"; let x = EvalEnv.update_val name rhs env in print_endline "updated"; x) with
        | Some env' -> st, env', SContinue
        | None -> raise_s [%message "name not found while assigning. Replace this with an insert_val call:" ~name:(name: Types.name)]
      end
    end
  | LMember{expr=lv;name=mname;} ->
    print_endline "assigninig to a member";
    print_endline ("member name is " ^ mname);
    begin match lv with
      | {lvalue = LName {name = BareName (_,"h")};_} -> print_endline "variable name is h"
      | _ -> () end;
    begin match EvalEnv.find_val (lv |> assert_lname) env with
      | VHeader _ -> print_endline "its a damn header for some dumb reason"
      | VLoc _ -> print_endline "its a fcking location like it should be"
      | VStruct _ -> print_endline "its a struct which is in the middle"
      | _ -> () end;
    let signal1, record = value_of_lvalue reader st env lv in
    begin match record with 
      | VStruct _ -> print_endline "<struct>"
      | VLoc l -> print_endline ("<loc>" ^ l) 
      | _ -> () end;
    let st, signal2 = update_member writer st record mname rhs inc_next in
    let record = match record with
      | VStack{headers; size; next} -> Bigint.(VStack {headers; size; next = next + (if inc_next then one else zero)})
      | _ -> rhs in
    begin match signal1, signal2 with
      | SContinue, SContinue ->
        assign_lvalue reader writer st env lv record inc_next
      | SContinue, _ -> st, env, signal2
      | _, _ -> st, env, signal1
    end
  | LBitAccess{expr=lv;msb;lsb;} ->
    let signal, bits = value_of_lvalue reader st env lv in
    begin match signal with
      | SContinue -> 
        assign_lvalue reader writer st env lv (update_slice bits msb lsb rhs) inc_next
      | _ -> st, env, signal
    end
  | LArrayAccess{expr=lv;idx;} ->
    let signal1, arr = value_of_lvalue reader st env lv in
    let idx = bigint_of_val idx in
    let st, signal2 = update_idx st arr idx rhs in
    begin match signal1, signal2 with
      | SContinue, SContinue -> 
        assign_lvalue reader writer st env lv arr inc_next
      | SContinue, _ -> st, env, signal2
      | _, _ -> st, env, signal1  
    end

and update_member (writer : 'a writer) (st : 'a State.t) (value : value) (fname : string)
    (fvalue : value) (inc_next : bool) : 'a State.t * signal =
  match value with
  | VStruct v ->
    print_endline "value is struct";
    update_field st v.fields fname fvalue, SContinue
  | VHeader v -> writer st v.is_valid v.fields fname fvalue, SContinue
  | VUnion {fields} ->
    update_union_member st fields fname fvalue
  | VStack{headers=hdrs; size=s; next=i} ->
    let idx = 
      match fname with
      | "next" -> i
      | "last" -> Bigint.(i - one)
      | _ -> failwith "BUG: VStack has no such member"
    in
    update_idx st value idx fvalue
  | VLoc l -> update_member writer st (State.find_heap l st) fname fvalue inc_next
  | _ -> failwith "member access undefined"

and update_union_member (st : 'a State.t) (fields : (string * loc) list)
    (member_name : string) (new_value : value) : 'a State.t * signal =
  let new_fields, new_value_valid = assert_header new_value in
  let set_validity st loc validity =
    let value = State.find_heap loc st in
    let value_fields, _ = assert_header value in
    State.insert_heap loc (VHeader {fields = value_fields; is_valid = validity}) st
  in
  let update_field st (name, loc) =
    if new_value_valid
    then if name = member_name
         then State.insert_heap loc new_value st
         else set_validity st loc false
    else set_validity st loc false
  in
  List.fold ~init:st ~f:update_field fields, SContinue

and update_field (st : 'a State.t) (fields : (string * loc) list) (field_name : string)
    (field_value : value) : 'a State.t =
  let update st (n,l) =
    if String.equal n field_name
    then State.insert_heap l field_value st
    else st in
  List.fold fields ~init:st ~f:update

and update_nth (st : 'a State.t) (l : loc list) (n : Bigint.t)
    (x : value) : 'a State.t =
  let n = Bigint.to_int_exn n in
  let xs, ys = List.split_n l n in
  match ys with
  | y :: ys -> State.insert_heap y x st
  | [] -> failwith "update_nth: out of bounds"

and update_idx (st : 'a State.t) (arr : value) (idx : Bigint.t)
    (value : value) : 'a State.t * signal =
  match arr with
  | VStack{headers; size; next} ->
     if Bigint.(idx < zero || idx >= size)
     then st, SReject "StackOutOfBounds"
     else update_nth st headers idx value, SContinue
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

  val externs : (string * extern) list

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern : 
    string -> ctrl -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> state * env * pkt option

end
