module I = Info
open Typed
open Prog
open Value
open Env
open Bitstring
open Core_kernel
module Info = I

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
  | TypeName n         -> init_val_of_typname env n false
  | TopLevelType n     -> init_val_of_typname env n true
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

and init_val_of_typname (env : env) (tname : string) (b : bool) : value =
  let t = 
    if b then EvalEnv.find_typ_toplevel tname env
    else EvalEnv.find_typ tname env in
  init_val_of_typ env t

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
      | TopLevelType n -> implicit_cast_from_tuple env v (EvalEnv.find_typ_toplevel n env)
      | _ -> VTuple l end
  | VRecord r -> failwith "TODO"
  | _ -> v

let rec value_of_lvalue (env : env) (lv : lvalue) : signal * value =
  match lv with
  | LName{name=n;_}                     -> SContinue, EvalEnv.find_val n env
  | LTopName{name=n;_}                  -> SContinue, EvalEnv.find_val_toplevel n env
  | LMember{expr=lv;name=n;_}           -> value_of_lmember env lv n
  | LBitAccess{expr=lv;msb=hi;lsb=lo;_} -> value_of_lbit env lv hi lo
  | LArrayAccess{expr=lv;idx;_}         -> value_of_larray env lv idx

and value_of_lmember (env : env) (lv : lvalue) (n : string) : signal * value =
  let (s,v) = value_of_lvalue env lv in
  let v' = match v with
    | VStruct{fields=l;_}
    | VHeader{fields=l;_}              ->
      List.Assoc.find_exn l n ~equal:String.equal
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

let rec assign_lvalue (env : env) (lhs : lvalue) (rhs : value) : env * signal =
  match lhs with
  | LName {name;typ} -> assign_name env name typ lhs rhs EvalEnv.insert_val, SContinue
  | LTopName {name;typ} -> assign_name env name typ lhs rhs EvalEnv.insert_val_toplevel, SContinue
  | LMember{expr=lv;name=mname;typ}    -> assign_member env typ lv mname rhs
  | LBitAccess{expr=lv;msb=m;lsb=l;_} -> assign_bitaccess env lv m l rhs
  | LArrayAccess{expr=lv;idx=e;typ}     -> assign_arrayaccess env typ lv e rhs

and assign_name (env : env) (name : string) (t : Type.t) (lhs : lvalue)
    (rhs : value) (f : string -> value -> env -> env) : env =
  match rhs with
  | VTuple l -> 
    f name (implicit_cast_from_tuple env rhs t) env
  | VStruct{fields} ->
    f name (VStruct{fields}) env
  | VHeader{fields;is_valid} -> 
    f name (VHeader{fields;is_valid}) env
  | VUnion{valid_header;valid_fields} -> 
    f name (VUnion{valid_header;valid_fields}) env
  | VStack{headers;size;next} -> 
    f name (VStack{headers;size;next}) env
  | VInteger n -> 
    f name (implicit_cast_from_rawint env rhs t) env
  | _ -> f name rhs env

and assign_member (env : env) (t : Type.t) (lv : lvalue) (mname : string)
    (rhs : value) : env * signal =
  let (s, v) = value_of_lvalue env lv in
  match s with 
  | SContinue -> 
    begin match v with
      | VStruct{fields=l} -> 
        assign_struct_mem env t lv rhs mname l
      | VHeader{fields=l;is_valid=b} ->
        assign_header_mem env t lv rhs mname l b
      | VUnion{valid_header=vs;valid_fields=bs} -> 
        assign_union_mem env t lv rhs mname bs
      | VStack{headers=hdrs;size=s;next=i} ->
        assign_stack_mem env t lv rhs mname hdrs s i
      | _ -> failwith "member access undefined" end
  | SExit | SReturn _ | SReject _ -> env, s

and assign_bitaccess (env : env) (lv : lvalue) (msb : Bigint.t) (lsb : Bigint.t)
    (rhs : value) : env * signal =
  let w = Bigint.(msb - lsb + one) in
  let (s, v) = value_of_lvalue env lv in
  match s with
  | SContinue ->
    let n = bigint_of_val v in
    let nw = width_of_val v in
    let rhs' = bit_of_rawint (bigint_of_val rhs) w |> bigint_of_val in
    let n0 = bitstring_slice n msb lsb in
    let diff = Bigint.(n0 - rhs') in
    let diff' = Bigint.(diff * (power_of_two lsb)) in
    let final = Bigint.(n - diff') in
    assign_lvalue env lv (VBit{w=nw;v=final})
  | SExit | SReturn _ | SReject _ -> env, s

and assign_arrayaccess (env : env) (t : Type.t) (lv : lvalue) (i : value)
    (rhs : value) : env * signal =
  let (s, v) = value_of_lvalue env lv in
  let i' = bigint_of_val i in
  let rhs' = implicit_cast_from_tuple env rhs t in
  let (env', signal) = match v with
    | VStack{headers=hdrs;size;next} ->
      let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn i') in
      begin match hdrs2 with
        | _ :: t ->
          let hdrs' = hdrs1 @ (rhs' :: t) in
          let rhs'' = VStack{headers=hdrs';size;next} in
          assign_lvalue env lv rhs''
        | [] -> (env, SReject "StackOutOfBounds") end
    | _ -> failwith "array access is not a header stack" in
  match signal with
  | SContinue -> env', signal
  | _ -> env, signal

and assign_struct_mem (env : env) (t : Type.t) (lhs : lvalue)
    (rhs : value) (fname : string)
    (l : (string * value) list) : env * signal =
  let rhs' = implicit_cast_from_rawint env rhs t in
  let rhs'' = implicit_cast_from_tuple env rhs' t in
  assign_lvalue env lhs (VStruct{fields=(fname, rhs'') :: l})

and assign_header_mem (env : env) (t : Type.t) (lhs : lvalue)
    (rhs : value) (fname : string) (l : (string * value) list)
    (b : bool) : env * signal =
  let rhs' = implicit_cast_from_rawint env rhs t in
  assign_lvalue env lhs (VHeader{fields=(fname,rhs') :: l;is_valid=b})

and assign_union_mem (env : env) (t : Type.t) (lhs : lvalue)
    (rhs : value) (fname : string) (vbs : (string * bool) list) : env * signal =
  let rhs' = implicit_cast_from_tuple env rhs t in
  let vbs' = List.map vbs ~f:(fun (s,_) -> (s, String.equal s fname)) in
  assign_lvalue env lhs (VUnion{valid_header=rhs'; valid_fields=vbs'})

and assign_stack_mem (env : env) (t : Type.t) (lhs : lvalue)
    (rhs : value) (mname : string) (hdrs : value list) 
    (size : Bigint.t) (next : Bigint.t) : env * signal =
  let () =
    match mname with
    | "next" -> ()
    | _ -> failwith "stack mem not an lvalue" in
  if Bigint.compare next size >= 0
  then (env, SReject "StackOutOfBounds")
  else
    let rhs' = implicit_cast_from_tuple env rhs t in
    let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn next) in
    let hdrs' =
      match hdrs2 with
      | _ :: t -> hdrs1 @ (rhs' :: t)
      | [] -> failwith "header stack is empty" in
    assign_lvalue env lhs (VStack{headers=hdrs';size;next})

module State = struct

  type 'a t = (int * 'a) list

  let empty = []

  let insert loc v st = (loc, v) :: st
  
  let find loc st = List.Assoc.find_exn (* TODO *) st loc ~equal:Int.equal

  let fresh_loc = 
    let counter = ref 0 in
    (fun () -> counter := !counter + 1; !counter)

end

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val eval_extern : ctrl -> env -> state -> Type.t list -> 
                    (value * Type.t) list -> string -> env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> state * env * pkt

end

module Core = struct

  type obj = 
    | PacketIn of pkt
    | PacketOut of pkt_out

  type state = obj State.t

  type extern = state pre_extern

  let assert_in (pkt : obj) : pkt =
    match pkt with
    | PacketIn p -> p
    | _ -> failwith "not a packetin"

  let value_of_field (init_fs : (string * value) list) 
      (f : RecordType.field) : string * value =
    f.name,
    List.Assoc.find_exn init_fs f.name ~equal:String.equal

  let nbytes_of_hdr (fs : (string * value) list) : Bigint.t =
    fs
    |> List.map ~f:snd
    |> List.map ~f:width_of_val
    |> List.fold_left ~init:Bigint.zero ~f:Bigint.(+)
    |> fun x -> Bigint.(x / ((one + one) * (one + one) * (one + one)))

  let bytes_of_packet (pkt : pkt) (nbytes : Bigint.t) : pkt * Bigint.t * signal =
    try
      let (c1,c2) = Cstruct.split pkt (Bigint.to_int_exn nbytes) in
      let s = Cstruct.to_string c1 in
      let chars = String.to_list s in
      let bytes = List.map chars ~f:Char.to_int in
      let bytes' = List.map bytes ~f:Bigint.of_int in
      let eight = Bigint.((one + one) * (one + one) * (one + one)) in
      let f a n = Bigint.(a * power_of_two eight + n) in
      let n = List.fold_left bytes' ~init:Bigint.zero ~f:f in
      (c2,n,SContinue)
    with Invalid_argument _ -> (pkt ,Bigint.zero,SReject "PacketTooShort")

  let rec extract_hdr_field (nvarbits : Bigint.t) (n, s : (Bigint.t * Bigint.t) * signal)
      (v : value) : ((Bigint.t * Bigint.t) * signal) * value =
    match s with
    | SContinue ->
      begin match v with
        | VBit{w;_} -> extract_bit n w
        | VInt{w;_} -> extract_int n w
        | VVarbit{max;_} -> extract_varbit nvarbits n max
        | _ -> failwith "invalid header field type" end
    | SReject _ -> ((n,s),VNull)
    | _ -> failwith "unreachable"

  and extract_bit (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue), VBit{w;v=x})

  and extract_int (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue), VInt{w;v=to_twos_complement x w})

  and extract_varbit (nbits : Bigint.t) (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    if Bigint.(nbits > w)
    then ((n,SReject "HeaderTooShort"),VNull)
    else
      let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-nbits) in
      let y = bitstring_slice nv Bigint.(nw-nbits-one) Bigint.zero in
      Bigint.(((nw-nbits, y), SContinue), VVarbit{max=w;w=nbits;v=x})

  let rec reset_fields (env : env) (fs : (string * value) list)
      (t : Type.t) : (string * value) list =
    match t with
    | Struct rt | Header rt -> List.map rt.fields ~f:(value_of_field fs)
    | TypeName n  -> reset_fields env fs (EvalEnv.find_typ n env)
    | TopLevelType n -> reset_fields env fs (EvalEnv.find_typ_toplevel n env)
    | NewType nt -> reset_fields env fs nt.typ
    | _ -> failwith "not resettable"

  let eval_extract' (ctrl : ctrl) (env : env) (st : state)
      (t : Type.t) (pkt : value) (v : value) (w : Bigint.t)
      (is_fixed : bool) : env * state * signal * value =
    let pkt_loc = 
      pkt
      |> assert_runtime in
    let pkt = State.find pkt_loc st |> assert_in in
    let init_fs = match v with
      | VHeader { fields; is_valid } -> fields
      | _ -> failwith "extract expects header" in
    let fs = reset_fields env init_fs t in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let nbytes = Bigint.(nbytes_of_hdr fs + w / eight) in
    let (pkt', extraction, s) = bytes_of_packet pkt nbytes in
    let st' = State.insert pkt_loc (PacketIn pkt') st in
    match s with
    | SReject _ | SExit | SReturn _ -> env, st, s, VNull
    | SContinue ->
      let (ns, vs) = List.unzip fs in
      let ((_,s), vs') =
        List.fold_map vs 
          ~init:(Bigint.(nbytes * eight, extraction), SContinue)
          ~f:(extract_hdr_field w) in
      begin match s with 
        | SReject _ | SExit | SReturn _ -> env, st', s, VNull
        | SContinue ->
          let fs' = List.zip_exn ns vs' in
          let h = VHeader {
            fields = fs';
            is_valid = true;
          } in
          let env'= 
            EvalEnv.insert_val 
              (if is_fixed then "hdr" else "variableSizeHeader")
              h env in
          env', st', SContinue, VNull
      end

  let eval_advance : extern = fun ctrl env st _ args ->
    let (pkt_loc, v) = match args with
      | [(VRuntime {loc;_}, _); (VBit{v;_}, _)] -> loc, v
      | _ -> failwith "unexpected args for advance" in
    let pkt = State.find pkt_loc st |> assert_in in
    try
      let x = (Bigint.to_int_exn v) / 8 in
      let pkt' = Cstruct.split pkt   x |> snd in
      let st' = State.insert pkt_loc (PacketIn pkt') st in
      env, st', SContinue, VNull
    with Invalid_argument _ ->
      env, st, SReject "PacketTooShort", VNull

  let eval_extract : extern = fun ctrl env st targs args ->
    match args with 
    | [(pkt, _);(v1, t)] -> eval_extract' ctrl env st t pkt v1 Bigint.zero true
    | [(pkt,_);(v1,t);(v2, _)] -> eval_extract' ctrl env st t pkt v1 (assert_bit v2 |> snd) false
    | [] -> eval_advance ctrl env st targs args
    | _ -> failwith "wrong number of args for extract"

  let rec width_of_typ (env : env) (t : Type.t) : Bigint.t =
    match t with
    | Bool -> Bigint.one
    | Int {width} | Bit {width} -> Bigint.of_int width
    | Array {typ;size} -> Bigint.(width_of_typ env typ * of_int size)
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
    | TopLevelType n -> width_of_typ env (EvalEnv.find_typ_toplevel n env)
    | NewType nt -> width_of_typ env nt.typ
    | _ -> failwith "not a fixed-width type"

  let rec val_of_bigint (env : env) (t : Type.t) (n : Bigint.t) : value =
    match t with
    | Bool -> if Bigint.(n = zero) then VBool false else VBool true
    | Int {width} -> 
      VInt {v = to_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Bit {width} ->
      VBit {v = of_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Array {typ;size} -> failwith "TODO: array of bigint"
    | Tuple _ -> failwith "TODO: tuple of bigint"
    | Record _ -> failwith "TODO: record_of_bigint"
    | Header _ -> failwith "TODO: header of bigint"
    | Struct _ -> failwith "TODO: struct of bigint"
    | Enum {typ = Some t;_} -> val_of_bigint env t n
    | TypeName name -> val_of_bigint env (EvalEnv.find_typ name env) n
    | TopLevelType name -> val_of_bigint env (EvalEnv.find_typ_toplevel name env) n
    | NewType nt -> val_of_bigint env nt.typ n
    | _ -> failwith "not a fixed-width type"
    
  let eval_lookahead : extern = fun _ env st targs args ->
    let t = match targs with
      | [t] -> t
      | _ -> failwith "unexpected type args for lookahead" in
    let w = width_of_typ env t in
    let pkt_loc = match args with
      | [(VRuntime {loc; _}, _)] -> loc
      | _ -> failwith "unexpected args for lookahead" in
    let pkt = State.find pkt_loc st |> assert_in in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    try
      let (pkt_hd, _) = Cstruct.split ~start:0 pkt Bigint.(to_int_exn (w/eight)) in
      let (_, n, _) = bytes_of_packet pkt_hd Bigint.(w/eight) in
      env, st, SContinue, val_of_bigint env t n
    with Invalid_argument _ -> env, st, SReject "PacketTooShort", VNull

  let eval_length : extern = fun _ env st _ args ->
    match args with
    | [(VRuntime {loc;_}, _)] ->
      let obj = State.find loc st in
      let len = 
        match obj with
        | PacketIn pkt -> Cstruct.len pkt
        | PacketOut _ -> failwith "expected packet_in" in
      env, st, SContinue, VBit {w= Bigint.of_int 32; v = Bigint.of_int len }
    | _ -> failwith "unexpected args for length"

  let packet_of_bytes (n : Bigint.t) (w : Bigint.t) : pkt =
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let seven = Bigint.(eight - one) in
    let rec h acc n w =
      if Bigint.(w = zero) then acc else
        let lsbyte = bitstring_slice n seven Bigint.zero in
        let n' = bitstring_slice n Bigint.(w-one) eight in
        h (lsbyte :: acc) n' Bigint.(w-eight) in
    let bytes = h [] n w in
    let ints = List.map bytes ~f:Bigint.to_int_exn in
    let chars = List.map ints ~f:Char.of_int_exn in
    let s = String.of_char_list chars in
    Cstruct.of_string s

  let rec field_types_of_typ (env : env) (t : Type.t) : Type.t list =
    match t with 
    | Header rt | Record rt | Struct rt -> List.map rt.fields ~f:(fun x -> x.typ)
    | TypeName n -> field_types_of_typ env (EvalEnv.find_typ n env)
    | TopLevelType n -> field_types_of_typ env (EvalEnv.find_typ n env)
    | NewType nt -> field_types_of_typ env nt.typ
    | _ -> failwith "type does not have fields"

  let rec packet_of_value (env : env) (t : Type.t) (v : value) : pkt =
    match v with
    | VBit {w; v} -> packet_of_bit w v
    | VInt {w; v} -> packet_of_int w v
    | VVarbit {max; w; v} -> packet_of_bit w v
    | VStruct {fields} -> packet_of_struct env t fields
    | VHeader {fields; is_valid} -> packet_of_hdr env t fields is_valid
    | VUnion {valid_header; valid_fields} -> packet_of_union env t valid_header valid_fields
    | VStack {headers; _} -> packet_of_stack env t headers
    | VInteger _ -> failwith "it was integer"
    | _ -> failwith "emit undefined on type"

  and packet_of_bit (w : Bigint.t) (v : Bigint.t) : pkt =
    packet_of_bytes v w

  and packet_of_int (w : Bigint.t) (v : Bigint.t) : pkt =
    packet_of_bytes (of_twos_complement v w) w

  and packet_of_struct (env : env) (t : Type.t)
      (fields : (string * value) list) : pkt =
    let fs = reset_fields env fields t in
    let fs' = List.map ~f:snd fs in
    let fts = field_types_of_typ env t in
    let pkts = List.map2_exn ~f:(fun v t -> packet_of_value env t v) fs' fts in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  and packet_of_hdr (env : env) (t : Type.t)
      (fields : (string * value) list) (is_valid : bool) : pkt =
    if is_valid then packet_of_struct env t fields else Cstruct.empty

  and packet_of_union (env : env) (t : Type.t) (hdr : value)
      (fs : (string * bool) list) : pkt =
    if List.exists fs ~f:snd
    then packet_of_value env t hdr
    else Cstruct.empty

  and packet_of_stack (env : env) (t : Type.t) (headers : value list) : pkt =
    let t' = match t with
      | Array at -> at.typ
      | _ -> failwith "expected array type" in
    let pkts = List.map ~f:(packet_of_value env t') headers in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  let eval_emit : extern = fun _ env st _ args ->
    let (pkt_loc, v, t) = match args with
      | [(VRuntime {loc; _}, _); (hdr, t)] -> loc, hdr, t
      | _ -> failwith "unexpected args for emit" in
    let (pkt_hd, pkt_tl) = match State.find pkt_loc st with
      | PacketOut (h, t) -> h, t
      | _ -> failwith "emit expected packet out" in
    let pkt_add = packet_of_value env t v in
    let emitted = Cstruct.append pkt_hd pkt_add, pkt_tl in
    let st' = State.insert pkt_loc (PacketOut emitted) st in
    env, st', SContinue, VNull

  let eval_verify : extern = fun _ env st _ args ->
    let b, err = match args with
      | [(VBool b, _); (VError err,_)] -> b, err
      | _ -> failwith "unexpected args for verify" in
    if b then env, st, SContinue, VNull
    else env, st, SReject err, VNull

  let externs : (string * extern) list =
    [ ("extract", eval_extract);
      ("lookahead", eval_lookahead);
      ("advance", eval_advance);
      ("length", eval_length);
      ("emit", eval_emit);
      ("verify", eval_verify)]

  let eval_extern ctrl env st vs name =
    let extern =
      match name with
      | "extract" -> eval_extract
      | "lookahead" -> eval_lookahead
      | "advance" -> eval_advance
      | "length" -> eval_length
      | "emit" -> eval_emit
      | "verify" -> eval_verify 
      | _ -> failwith "extern undefined" in
    extern ctrl env st vs

end 

module V1Model : Target = struct

  type obj =
    | CoreObject of Core.obj
    | V1Object of v1object

  and v1object =
    | Counter of {
        states : Bigint.t list;
        typ : counter_type;
        size : Bigint.t;
      }

  and counter_type =
    (* | Packets *)
    (* | Bytes *)
    | Both

  let x = Counter {states = []; typ = Both; size = Bigint.zero}
  let _ = V1Object x

  type state = obj State.t
  type extern = state pre_extern

  let assert_pkt = function
    | CoreObject (PacketIn pkt) -> pkt
    | CoreObject _ | V1Object _ -> failwith "not a packet"

  let assert_core = function
    | CoreObject o -> o
    | V1Object _ -> failwith "expected core object"

  let is_core = function
    | CoreObject _ -> true
    | V1Object _ -> false

  let eval_counter : extern = fun ctrl env st args ->
    (* let counter_loc = State.fresh_loc () in state persistence? *)
    failwith "TODO"

  let eval_count : extern = fun _ -> failwith "TODO"

  let eval_direct_counter : extern = fun _ -> failwith "TODO"

  let eval_meter : extern = fun _ -> failwith "TODO"

  let eval_execute_meter : extern = fun _ -> failwith "TODO"

  let eval_direct_meter : extern = fun _ -> failwith "TODO"

  let eval_read : extern = fun _ -> failwith "TODO"

  let eval_register : extern = fun _ -> failwith "TODO"

  let eval_write : extern = fun _ -> failwith "TODO"

  let eval_action_profile : extern = fun _ -> failwith "TODO"

  let eval_random : extern = fun _ -> failwith "TODO"

  let eval_digest : extern = fun _ -> failwith "TODO"

  let eval_mark_to_drop : extern = fun _ -> failwith "TODO"

  let eval_hash : extern = fun _ -> failwith "TODO"

  let eval_action_selector : extern = fun _ -> failwith "TODO"

  let eval_checksum16 : extern = fun _ -> failwith "TODO"

  let eval_get : extern = fun _ -> failwith "TODO"

  let eval_verify_checksum : extern = fun _ -> failwith "TODO"

  let eval_update_checksum : extern = fun _ -> failwith "TODO"

  let eval_verify_checksum_with_payload : extern = fun _ -> failwith "TODO"

  let eval_update_checksum_with_payload : extern = fun _ -> failwith "TODO"

  let eval_resubmit : extern = fun _ -> failwith "TODO"

  let eval_recirculate : extern = fun _ -> failwith "TODO"

  let eval_clone : extern = fun _ -> failwith "TODO"

  let eval_clone3 : extern = fun _ -> failwith "TODO"

  let eval_truncate : extern = fun _ -> failwith "TODO"

  let eval_assert : extern = fun _ -> failwith "TODO"

  let eval_assume : extern = fun _ -> failwith "TODO"

  let eval_log_msg : extern = fun _ -> failwith "TODO"

  let v1externs = [
    ("counter", eval_counter);
    ("count", eval_count); (* overloaded *)
    ("direct_counter", eval_direct_counter);
    ("meter", eval_meter);
    ("execute_meter", eval_execute_meter);
    ("direct_meter", eval_direct_meter);
    ("read", eval_read); (* overloaded*)
    ("register", eval_register);
    ("write", eval_write);
    ("action_profile", eval_action_profile);
    ("random", eval_random);
    ("digest", eval_digest);
    ("mark_to_drop", eval_mark_to_drop); (* overloaded, deprecated *)
    ("hash", eval_hash);
    ("action_selector", eval_action_selector);
    ("Checksum16", eval_checksum16); (* deprecated *)
    ("get", eval_get); (* deprecated *)
    ("verify_checksum", eval_verify_checksum);
    ("update_checksum", eval_update_checksum);
    ("verify_checksum_with_payload", eval_verify_checksum_with_payload);
    ("update_checksum_with_payload", eval_update_checksum_with_payload);
    ("resubmit", eval_resubmit);
    ("recirculate", eval_recirculate);
    ("clone", eval_clone);
    ("clone3", eval_clone3);
    ("truncate", eval_truncate);
    ("assert", eval_assert);
    ("assume", eval_assume);
    ("log_msg", eval_log_msg); (* overloaded *)
  ]

  let corize_st (st : state) : Core.state =
    st
    |> List.filter ~f:(fun (_, o) -> is_core o)
    |> List.map ~f:(fun (i, o) -> (i, assert_core o))

  let targetize_st (st : Core.state) : state = 
    st
    |> List.map ~f:(fun (i, o) -> i, CoreObject o)

  let targetize (ext : Core.extern) : extern =
    fun ctrl env st ts vs ->
    let (env', st', s, v) =
      ext ctrl env (corize_st st) ts vs in
    env', targetize_st st' @ st, s, v

  let externs : (string * extern) list =
    v1externs @ (List.map Core.externs ~f:(fun (n, e : string * Core.extern) -> n, targetize e))

  let eval_extern ctrl env st targs args name =
    let extern =
      match name with
      | "extract" -> targetize Core.eval_extract
      | "lookahead" -> targetize Core.eval_lookahead
      | "advance" -> targetize Core.eval_advance
      | "length" -> targetize Core.eval_length
      | "emit" -> targetize Core.eval_emit
      | "verify" -> targetize Core.eval_verify
      | _ -> failwith "TODO" in
    extern ctrl env st targs args

  let initialize_metadata meta env =
    let nine = Bigint.of_int 9 in
    EvalEnv.insert_val "ingress_port" (VBit{w=nine; v=meta}) env

  let check_pipeline env = ()

  let eval_v1control (ctrl : ctrl) (app) (control : value)
      (args : Expression.t option list) (env,st) : env * state * signal =
    let (env,st',s,_) = app ctrl env st SContinue control args in
    (env,st',s)

  let eval_pipeline
        (ctrl: ctrl)
        (env: env)
        (st: obj State.t)
        (pkt: pkt)
        (app: state apply) =
    let in_port = EvalEnv.find_val "ingress_port" env |> assert_bit |> snd in 
    let fst23 (a,b,_) = (a,b) in  
    let main = EvalEnv.find_val "main" env in
    let vs = assert_package main |> snd in
    let parser =
      List.Assoc.find_exn vs "p"   ~equal:String.equal in
    let verify =
      List.Assoc.find_exn vs "vr"  ~equal:String.equal in
    let ingress =
      List.Assoc.find_exn vs "ig"  ~equal:String.equal in
    let egress =
      List.Assoc.find_exn vs "eg"  ~equal:String.equal in
    let compute =
      List.Assoc.find_exn vs "ck"  ~equal:String.equal in
    let deparser =
      List.Assoc.find_exn vs "dep" ~equal:String.equal in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let pkt_loc = State.fresh_loc () in
    let vpkt = VRuntime { loc = pkt_loc; typ_name = "packet_in"; } in
    let st = State.insert pkt_loc (CoreObject (PacketIn pkt)) st in
    let hdr =
      init_val_of_typ env (snd (List.nth_exn params 1)).typ in
    let meta =
      init_val_of_typ env (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init_val_of_typ env (snd (List.nth_exn params 3)).typ in
    let env =
      EvalEnv.(env
              |> insert_val "packet"   vpkt
              |> insert_val "hdr"      hdr
              |> insert_val "meta"     meta
              |> insert_val "std_meta" std_meta
              |> insert_typ "packet"   (snd (List.nth_exn params 0)).typ
              |> insert_typ "hdr"      (snd (List.nth_exn params 1)).typ
              |> insert_typ "meta"     (snd (List.nth_exn params 2)).typ
              |> insert_typ "std_meta" (snd (List.nth_exn params 3)).typ) in
    (* TODO: implement a more responsible way to generate variable names *)
    let nine = Bigint.((one + one + one) * (one + one + one)) in
    let (env, _) = 
      assign_lvalue 
        env
        (LMember{expr=LName{name = "std_meta";typ = (snd (List.nth_exn params 3)).typ}; name="ingress_port"; typ = Bit {width = 9};})
        (VBit{w=nine;v=in_port}) in
    let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = (Name (Info.dummy, "packet")); dir = InOut; typ = (snd (List.nth_exn params 0)).typ}) in
    let hdr_expr =
      Some (Info.dummy, {expr = (Name (Info.dummy, "hdr")); dir = InOut; typ = (snd (List.nth_exn params 1)).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = (Name (Info.dummy, "meta")); dir = InOut; typ = (snd (List.nth_exn params 2)).typ}) in
    let std_meta_expr =
      Some (Info.dummy, {expr = (Name (Info.dummy, "std_meta")); dir = InOut; typ = (snd (List.nth_exn params 3)).typ}) in
    let (env, st, state,_) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let (env,st) =
      match state with 
      | SReject err -> 
        assign_lvalue env (LMember{expr=LName{name = "std_meta"; typ = (snd (List.nth_exn params 3)).typ};name="parser_error"; typ = Error}) (VError(err))
        |> fst, st
      | SContinue -> (env,st)
      | _ -> failwith "parser should not exit or return" in
    let pktout_loc = State.fresh_loc () in 
    let vpkt' = VRuntime { loc = pktout_loc; typ_name = "packet_out"; } in
    let st = 
      State.insert 
        pktout_loc 
        (CoreObject (PacketOut (Cstruct.create 0, State.find pkt_loc st
                                                  |> assert_pkt))) st in
    let env = EvalEnv.insert_val "packet" vpkt' env in
    let env = EvalEnv.insert_typ "packet" (snd (List.nth_exn deparse_params 0)).typ env in
    let (env,st,_) = 
      (env,st)
      |> eval_v1control ctrl app verify   [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app compute  [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app deparser [pkt_expr; hdr_expr] in
    match EvalEnv.find_val "packet" env with
    | VRuntime {loc; _ } -> 
      begin match State.find loc st with 
        | CoreObject (PacketOut(p0,p1)) -> st, env, Cstruct.append p0 p1
        | _ -> failwith "not a packet" 
      end
    | _ -> failwith "pack not a packet"

end

module EbpfFilter : Target = struct 

  type obj = unit (* TODO *)

  type state = obj State.t

  type extern = state pre_extern

  let externs = []

  let eval_extern _ = failwith ""

  let initialize_metadata meta env =
    env (* TODO *)

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
  (env,st) : env * state * signal =
    let (env,st,s,_) = app ctrl env st SContinue control args in 
    (env,st,s)

  let eval_pipeline ctrl env st pkt app = failwith "TODO"
    (* let main = EvalEnv.find_val "main" env in
    let vs = assert_package main |> snd in
    let parser = List.Assoc.find_exn vs "prs"  ~equal:String.equal in
    let filter = List.Assoc.find_exn vs "filt" ~equal:String.equal in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let 
    let pckt = VRuntime (PacketIn pkt) in
    let hdr = init_val_of_typ env (snd (List.nth_exn params 1)).typ in
    let accept = VBool (false) in
    let env =
      EvalEnv.(env
               |> insert_val "packet" pckt
               |> insert_val "hdr"    hdr
               |> insert_val "accept" accept
               |> insert_typ "packet" (snd (List.nth_exn params 0)).typ
               |> insert_typ "hdr"    (snd (List.nth_exn params 1)).typ
               |> insert_typ "accept" (Info.dummy, Type.Bool)) in
    let pckt_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
    let hdr_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
    let accept_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "accept"))}) in
    let (env, st,state, _) =
      app ctrl env st SContinue parser [pckt_expr; hdr_expr] in
    let fst23 (a,b,_) = (a,b) in
    let (env,st) = 
      match state with 
      | SReject _ -> assign_lvalue ctrl env st (LName("accept")) (VBool(false)) |> fst23
      | SContinue ->  (env,st) |> eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app |> fst23 
      | _ -> failwith "parser should not exit or return" in
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1) *)
    (* | _ -> failwith "pack not a packet" *)

end
