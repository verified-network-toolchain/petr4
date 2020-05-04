module I = Info
open Typed
open Prog
open Value
open Env
open Core_kernel
module Info = I

type env = EvalEnv.t

type 'st assign = env -> lvalue -> value -> env * signal

type ('st1, 'st2) pre_extern =
  'st1 assign -> ctrl -> env -> 'st2 -> Type.t list -> (value * Type.t) list ->
  env * 'st2 * signal * value

type 'st apply =
  ctrl -> env -> 'st -> signal -> value -> Expression.t option list -> env * 'st * signal * value

type 'st init_typ = 
  env -> Type.t -> value

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

  type 'st extern = ('st, state) pre_extern

  val externs : (string * state extern) list

  val eval_extern : state assign -> ctrl -> env -> state -> Type.t list -> 
                    (value * Type.t) list -> string -> env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> 
  state assign -> state init_typ -> state * env * pkt

end

module Core = struct

  type obj = 
    | PacketIn of pkt
    | PacketOut of pkt_out

  type state = obj State.t

  type 'st extern = ('st, state) pre_extern

  let rec shift_bigint_left (v : Bigint.t) (o : Bigint.t) : Bigint.t =
    if Bigint.(o > zero)
    then shift_bigint_left Bigint.(v * (one + one)) Bigint.(o - one)
    else v

  let power_of_two (w : Bigint.t) : Bigint.t =
    shift_bigint_left Bigint.one w

  let rec to_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
    let two = Bigint.(one + one) in
    let w' = power_of_two w in
    if Bigint.(n >= (w' / two))
    then to_twos_complement Bigint.(n-w') w
    else if Bigint.(n < -(w'/two))
    then to_twos_complement Bigint.(n+w') w
    else n
    
  let rec of_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
    let w' = power_of_two w in
    if Bigint.(n >= w')
    then Bigint.(n % w')
    else if Bigint.(n < zero)
    then of_twos_complement Bigint.(n + w') w
    else n

  let rec bitstring_slice (n : Bigint.t) (m : Bigint.t) (l : Bigint.t) : Bigint.t =
    Bigint.(
      if l > zero
      then bitstring_slice (n/(one + one)) (m-one) (l-one)
      else n % (power_of_two (m + one)))

  let assert_in (pkt : obj) : pkt =
    match pkt with
    | PacketIn p -> p
    | _ -> failwith "not a packetin"

  let value_of_field (init_fs : (string * value) list) 
      (f : RecordType.field) : string * value =
    f.name,
    List.Assoc.find_exn init_fs f.name ~equal:String.equal

  let width_of_val (v : value) : Bigint.t = 
    match v with
    | VBit {w; _} | VInt {w; _} -> w
    | VVarbit _ -> Bigint.zero
    | _ -> failwith "illegal header field type"

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

  let eval_extract' (assign : 'st assign) (ctrl : ctrl) (env : env) (st : state)
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
          (* begin match List.Assoc.find fs' "ethernet" ~equal:String.equal with
          | None -> print_endline "didnt get initialized by extract"
          | Some _ -> print_endline "got initialized by extract" end; *)
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

  let eval_advance : 'st extern = fun assign ctrl env st _ args ->
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

  let eval_extract : 'st extern = fun assign ctrl env st targs args ->
    (* print_endline "doing extract"; *)
    match args with 
    | [(pkt, _);(v1, t)] -> eval_extract' assign ctrl env st t pkt v1 Bigint.zero true
    | [(pkt,_);(v1,t);(v2, _)] -> eval_extract' assign ctrl env st t pkt v1 (assert_bit v2 |> snd) false
    | [] -> eval_advance assign ctrl env st targs args
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
    
  let eval_lookahead : 'st extern = fun _ _ env st targs args ->
    (* print_endline "doing lookahead"; *)
    let t = match targs with
      | [t] -> t
      | _ -> failwith "unexpected type args for lookahead" in
    (* let t = Typed.Type.Void TODO in *)
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

  let eval_length : 'st extern = fun _ _ env st _ args ->
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
    (* print_endline "getting packet of bytes"; *)
    (* print_string "width is:"; print_endline (Bigint.to_string w); *)
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

  let rec of_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
    let w' = power_of_two w in
    if Bigint.(n >= w')
    then Bigint.(n % w')
    else if Bigint.(n < zero)
    then of_twos_complement Bigint.(n + w') w
    else n

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
    (* print_endline "got to packet_of_bit"; *)
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
    print_endline "emitting header";
    if is_valid then (print_endline "was valid"; packet_of_struct env t fields) else Cstruct.empty

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

  let eval_emit : 'st extern = fun _ _ env st _ args ->
    print_endline "doing emit";
    let (pkt_loc, v, t) = match args with
      | [(VRuntime {loc; _}, _); (hdr, t)] -> loc, hdr, t
      | _ -> failwith "unexpected args for emit" in
    let (pkt_hd, pkt_tl) = match State.find pkt_loc st with
      | PacketOut (h, t) -> h, t
      | _ -> failwith "emit expected packet out" in
    (* print_endline "getting pkt_add"; *)
    (* begin match v with
    | VBit {w;_} -> print_string "width is now: "; print_endline (Bigint.to_string w)
    | _ -> () end ; *)
    let pkt_add = packet_of_value env t v in
    (* print_endline "got pkt_add"; *)
    let emitted = Cstruct.append pkt_hd pkt_add, pkt_tl in
    (* print_endline "appended"; *)
    let st' = State.insert pkt_loc (PacketOut emitted) st in
    (* print_endline "updated state"; *)
    env, st', SContinue, VNull

  let eval_verify : 'st extern = fun _ _ env st _ args ->
    let b, err = match args with
      | [(VBool b, _); (VError err,_)] -> b, err
      | _ -> failwith "unexpected args for verify" in
    if b then env, st, SContinue, VNull
    else env, st, SReject err, VNull

  let externs : (string * 'st extern) list =
    [ ("extract", eval_extract);
      ("lookahead", eval_lookahead);
      ("advance", eval_advance);
      ("length", eval_length);
      ("emit", eval_emit);
      ("verify", eval_verify)]

  let eval_extern assign ctrl env st vs name =
    let extern =
      match name with
      | "extract" -> eval_extract
      | "lookahead" -> eval_lookahead
      | "advance" -> eval_advance
      | "length" -> eval_length
      | "emit" -> eval_emit
      | "verify" -> eval_verify 
      | _ -> failwith "extern undefined" in
    extern assign ctrl env st vs

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
  type 'st extern = ('st, state) pre_extern

  let assert_pkt = function
    | CoreObject (PacketIn pkt) -> pkt
    | CoreObject _ | V1Object _ -> failwith "not a packet"

  let assert_core = function
    | CoreObject o -> o
    | V1Object _ -> failwith "expected core object"

  let is_core = function
    | CoreObject _ -> true
    | V1Object _ -> false

  let eval_counter : state extern = fun assign ctrl env st args ->
    (* let counter_loc = State.fresh_loc () in state persistence? *)
    failwith "TODO"

  let eval_count : state extern = fun _ -> failwith "TODO"

  let eval_direct_counter : state extern = fun _ -> failwith "TODO"

  let eval_meter : state extern = fun _ -> failwith "TODO"

  let eval_execute_meter : state extern = fun _ -> failwith "TODO"

  let eval_direct_meter : state extern = fun _ -> failwith "TODO"

  let eval_read : state extern = fun _ -> failwith "TODO"

  let eval_register : state extern = fun _ -> failwith "TODO"

  let eval_write : state extern = fun _ -> failwith "TODO"

  let eval_action_profile : state extern = fun _ -> failwith "TODO"

  let eval_random : state extern = fun _ -> failwith "TODO"

  let eval_digest : state extern = fun _ -> failwith "TODO"

  let eval_mark_to_drop : state extern = fun _ -> failwith "TODO"

  let eval_hash : state extern = fun _ -> failwith "TODO"

  let eval_action_selector : state extern = fun _ -> failwith "TODO"

  let eval_checksum16 : state extern = fun _ -> failwith "TODO"

  let eval_get : state extern = fun _ -> failwith "TODO"

  let eval_verify_checksum : state extern = fun _ -> failwith "TODO"

  let eval_update_checksum : state extern = fun _ -> failwith "TODO"

  let eval_verify_checksum_with_payload : state extern = fun _ -> failwith "TODO"

  let eval_update_checksum_with_payload : state extern = fun _ -> failwith "TODO"

  let eval_resubmit : state extern = fun _ -> failwith "TODO"

  let eval_recirculate : state extern = fun _ -> failwith "TODO"

  let eval_clone : state extern = fun _ -> failwith "TODO"

  let eval_clone3 : state extern = fun _ -> failwith "TODO"

  let eval_truncate : state extern = fun _ -> failwith "TODO"

  let eval_assert : state extern = fun _ -> failwith "TODO"

  let eval_assume : state extern = fun _ -> failwith "TODO"

  let eval_log_msg : state extern = fun _ -> failwith "TODO"

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

  let corize_assign (assign : state assign) : Core.state assign =
    fun env lv v ->
    let (env, s) = assign env lv v in
    env, s

  let targetize (ext : Core.state Core.extern) : state extern =
    fun assign ctrl env st ts vs ->
    let (env', st', s, v) =
      ext (corize_assign assign) ctrl env (corize_st st) ts vs in
    env', targetize_st st' @ st, s, v

  let externs : (string * state extern) list =
    v1externs @ (List.map Core.externs ~f:(fun (n, e : string * 'st Core.extern) -> n, targetize e))

  let eval_extern assign ctrl env st targs args name =
    (* print_endline "finding extern"; *)
    let extern =
      match name with
      | "extract" -> targetize Core.eval_extract
      | "lookahead" -> targetize Core.eval_lookahead
      | "advance" -> targetize Core.eval_advance
      | "length" -> targetize Core.eval_length
      | "emit" -> targetize Core.eval_emit
      | "verify" -> targetize Core.eval_verify
      | _ -> failwith "TODO" in
    (* print_endline "found extern"; *)
    extern assign ctrl env st targs args

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
        (app: state apply )
        (assign: state assign)
        (init: state init_typ) =
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
      init env (snd (List.nth_exn params 1)).typ in
    let meta =
      init env (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init env (snd (List.nth_exn params 3)).typ in
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
      assign 
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
        assign env (LMember{expr=LName{name = "std_meta"; typ = (snd (List.nth_exn params 3)).typ};name="parser_error"; typ = Error}) (VError(err))
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
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
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

  type 'st extern = ('st, state) pre_extern

  let externs = []

  let eval_extern _ = failwith ""

  let initialize_metadata meta env =
    env (* TODO *)

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
  (env,st) : env * state * signal =
    let (env,st,s,_) = app ctrl env st SContinue control args in 
    (env,st,s)

  let eval_pipeline ctrl env st pkt app assign init = failwith "TODO"
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
    let hdr = init ctrl env st (snd (List.nth_exn params 1)).typ in
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
      | SReject _ -> assign ctrl env st (LName("accept")) (VBool(false)) |> fst23
      | SContinue ->  (env,st) |> eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app |> fst23 
      | _ -> failwith "parser should not exit or return" in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1) *)
    (* | _ -> failwith "pack not a packet" *)

end
