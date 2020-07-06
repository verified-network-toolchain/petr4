open Typed
open Prog
open Value
open Env
open Target
open Error
module I = Info
module H = Hash
open Core_kernel
module Info = I
module Hash = H

module PreV1Switch : Target = struct

  let drop_spec = Bigint.of_int 511

  type obj =
    | Counter of {
        typ : counter_type;
        size : Bigint.t;
      }
    | DirectCounter of {
      typ : counter_type;
    }
    | Meter of unit (* TODO *)
    | DirectMeter of unit (* TODO *)
    | Register of {
        states: value list;
        size: Bigint.t;
      }
    | ActionProfile of unit (* TODO *)
    | ActionSelector of unit (* TODO *)
    | Checksum16 of unit (* TODO *)

  and counter_type =
    | Packets of Bigint.t list
    | Bytes of Bigint.t list
    (* packet count, byte count *)
    | Both of (Bigint.t * Bigint.t) list

  type state = obj State.t
  type extern = state pre_extern

  let read_header_field : obj reader = fun is_valid fields fname ->
    List.Assoc.find_exn fields fname ~equal:String.equal

  let write_header_field : obj writer = fun is_valid fields fname fvalue ->
    let fs = List.map fields
      ~f:(fun (n,v) -> if String.equal n fname then n, fvalue else n,v) in
    VHeader {fields = fs; is_valid; }

  let assign_lvalue = assign_lvalue read_header_field write_header_field

  let eval_counter : extern = fun env st ts args ->
    let (loc, v, typ) = match args with 
      | [(VRuntime {loc; _}, _);
        (VBit {v; _},_);
        (VEnumField{enum_name; _}, _)] -> loc, v, enum_name
      | _ -> failwith "unexpected args for counter instantiation" in
    let size = Bigint.to_int_exn v in
    let ctr_typ = match typ with
      | "packets" ->
        Packets (List.init size ~f:(fun _ -> Bigint.zero))
      | "bytes" ->
        Bytes (List.init size ~f:(fun _ -> Bigint.zero))
      | "packets_and_bytes" ->
        Both (List.init size ~f:(fun _ -> Bigint.zero, Bigint.zero))
      | _ -> failwith "unexpected field name for counter type" in
    let ctr = Counter { typ = ctr_typ; size = Bigint.of_int size; } in
    env, State.insert_extern loc ctr st, SContinue, VRuntime {loc = loc; obj_name = "counter"}
      
  let eval_count_counter : extern = fun env st ts args ->
    let (loc, v) = match args with
      | [(VRuntime{loc;_},_); (VBit {v;_}, _)] -> loc, Bigint.to_int_exn v
      | _ -> failwith "unexpected args for count counter" in
    let pkt_len = (State.get_packet st).in_size |> Bigint.of_int in
    let ctr = State.find_extern loc st in
    let ctr' = match ctr with
      | Counter {size; typ = Packets l} ->
        Counter {size; typ = Packets begin
          List.mapi l ~f:(fun i n -> Bigint.(if Int.equal i v then n + one else n))
        end }
      | Counter {size; typ = Bytes l} ->
        Counter {size; typ = Bytes begin
          List.mapi l ~f:(fun i n -> Bigint.(if Int.equal i v then n + pkt_len else n))
        end }
      | Counter {size; typ = Both l} ->
        Counter {size; typ = Both begin
          List.mapi l
            ~f:(fun i (p,b) -> Bigint.(if Int.equal i v then p+one, b + pkt_len else p, b))
        end }
      | _ -> failwith "cannot perform a count on a non-counter object" in
    env, State.insert_extern loc ctr' st, SContinue, VNull

  let eval_count_direct_counter : extern = fun env st ts args ->
    (* actual direct counting implemented in target-dependent table execution *)
    env, st, SContinue, VNull

  let eval_count : extern = fun env st ts args ->
    match args with 
    | [_;_] -> eval_count_counter env st ts args
    | [_;] -> eval_count_direct_counter env st ts args
    | _ -> failwith "unexpected args for count"

  let eval_direct_counter : extern = fun env st ts args ->
    match args with
    | [(VRuntime{loc;obj_name}, _); (VEnumField{enum_name;_}, _);] ->
      let dctr = match enum_name with
        | "packets" -> DirectCounter {typ = Packets []}
        | "bytes" -> DirectCounter {typ = Bytes []}
        | "packets_and_bytes" -> DirectCounter {typ = Both []}
        | _ -> failwith "unexpected field name for counter type" in
      env, State.insert_extern loc dctr st, SContinue, VRuntime{loc;obj_name}
    | _ -> failwith "unexpected args for direct counter"

  let eval_meter : extern = fun env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with
      | [(VRuntime{loc;obj_name},_); _; _] -> loc, obj_name
      | _ -> failwith "unexpected args for meter" in
    let meter = Meter () in
    env, State.insert_extern loc meter st, SContinue, VRuntime{loc;obj_name}

  let eval_execute_meter : extern = fun env st ts args ->
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_direct_meter : extern = fun env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with
      | [(VRuntime{loc;obj_name},_); _] -> loc,obj_name
      | _ -> failwith "unexpected args for direct meter instantiation" in
    let dmeter = DirectMeter () in
    env, State.insert_extern loc dmeter st, SContinue, VRuntime{loc;obj_name}

  let eval_register_read : extern = fun env st _ args ->
    match args with
    | [(VRuntime {loc;_}, _); (_,t) ; (VBit {w = w; v = v}, _)] ->
      let reg_obj = State.find_extern loc st in
      let states = match reg_obj with
        | Register {states; _} -> states
        | _ -> failwith "Reading from an object other than a v1 register" in
      let read_val =
        Bigint.to_int_exn v
        |> List.nth_exn states
        |> Ops.interp_cast ~type_lookup:(fun name -> EvalEnv.find_typ name env) t in
      (* let read_val = State.find_heap read_loc st in *)
      let l = State.fresh_loc () in
      let st = State.insert_heap l read_val st in
      let env = EvalEnv.insert_val (Types.BareName (Info.dummy, "result")) l env in 
      env, st, SContinue, read_val
    | _ -> failwith "unexpected args for register read"

  
  
  let eval_meter_read : extern = fun env st ts args ->
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_read : extern = fun env st ts args ->
    match args with 
    | [ _; _; _] -> eval_register_read env st ts args
    | [ _; _;] -> eval_meter_read env st ts args
    | _ -> failwith "unexpected read args"
    
  let eval_register : extern = fun env st typs args ->
    let typ = Typed.Type.Bit {width = 32} in
    match args with
    | [(VRuntime {loc;obj_name}, _); (VBit {w = _; v = size}, _)]
    | [(VRuntime {loc;obj_name}, _); (VInteger size, _)] -> (* TODO: shouldnt be needed*)
      let init_val = init_val_of_typ env typ in
      let states = List.init (Bigint.to_int_exn size) ~f:(fun _ -> init_val) in
      let reg = Register {states = states;
                          size = size; } in
      let st' = State.insert_extern loc reg st in
      env, st', SContinue, VRuntime {loc = loc; obj_name = obj_name}
    | _ -> failwith "unexpected args for register instantiation"

  let eval_write : extern = fun env st _ args -> 
    match args with
    | [(VRuntime {loc;_}, _); 
        (VBit {w = _; v = v_index}, _) ; 
        (write_val, _)] ->
      let reg_obj = State.find_extern loc st in
      let states, size = match reg_obj with
        | Register {states; size} -> states, size
        | _ -> failwith "Reading from an object other than a v1 register" in
      let subs_f = fun i v -> 
        if Bigint.(of_int i = v_index) then write_val else v in 
      let states = List.mapi ~f:subs_f states in
      let reg_obj = Register {states; size} in
      let st = State.insert_extern loc reg_obj st in
      env, st, SContinue, write_val 
    | _ -> failwith "unexpected args for register write"

  let eval_action_profile : extern = fun env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with 
      | [(VRuntime{loc;obj_name},_); _] -> loc, obj_name
      | _ -> failwith "unexpected args for action profile" in
    let prof = ActionProfile () in
    env, State.insert_extern loc prof st, SContinue, VRuntime{loc;obj_name}

  let eval_random : extern = fun env st ts args ->
    Random.self_init ();
    let width = match ts with
      | [Bit{width}] -> Bigint.of_int width
      | _ -> failwith "unexpected type args for random" in
    let (lo,hi) = match args with
      | [_; (VBit{v=lo;_}, _); (VBit{v=hi;_}, _)] ->
        Bigint.to_int_exn lo, Bigint.to_int_exn hi
      | _ -> failwith "unexpected args for random" in
    let random_int = try Random.int_incl lo hi with _ -> 0 in
    let random_val = VBit{w=width; v=Bigint.of_int random_int} in
    let l = State.fresh_loc () in
    let st = State.insert_heap l random_val st in
    let env' = EvalEnv.insert_val (BareName (Info.dummy, "result")) l env in
    env', st, SContinue, VNull
        
  let eval_digest : extern = fun env st ts args ->
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_mark_to_drop : extern = fun env st ts args ->
    let _ = match args with
      | [] -> failwith "deprecated version of mark to drop"
      | _ -> () in
    let lv = {
      lvalue = LMember {
        expr = {
          lvalue = LName {name = BareName (Info.dummy, "standard_metadata")};
          typ = TypeName (BareName (Info.dummy, "standard_metadata_t"));
        };
        name = "egress_spec";
      };
      typ = Bit{width=9};
    } in
    let (st, _) =
      assign_lvalue st env lv (VBit {v = drop_spec; w = Bigint.of_int 9}) in
    env, st, SContinue, VNull

  let package_for_hash (st : state) (data : value list) : Bigint.t * Bigint.t =
    data
    |> List.map ~f:(fun v -> width_of_val v, bigint_of_val v)
    |> List.map ~f:(fun (w,v) -> w, Bitstring.of_twos_complement v w)
    |> List.fold ~init:Bigint.(zero,zero) ~f:(fun (accw, accv) (nw, nv) ->
        Bigint.(accw + nw, Bitstring.shift_bitstring_left accv nw + nv))

  let adjust_hash_value : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t =
    fun base rmax hv ->
    if Bigint.(rmax = zero)
    then base
    else if Bigint.(rmax >= one)
    then Bigint.((hv % (rmax - base)) + base)
    else base (* TODO: behavior in this case is unspecified *)

  let eval_hash : extern = fun env st ts args ->
    let width = match ts with
      | o :: _ -> width_of_typ env o
      | _ -> failwith "missing type args for hash" in
    let (algo, base, data, rmax) = match args with
      | [_; (VEnumField {enum_name=algo;_}, _);
        (VBit{v=base;_},_); (VTuple data, _); (VBit{v=max;_}, _)] ->
        algo, base, data, max
      | _ -> failwith "unexpected args for hash" in
    let result = 
      data
      |> package_for_hash st
      |> Hash.hash algo
      |> adjust_hash_value base rmax in
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VBit{w=width; v=Bitstring.of_twos_complement result width}) st in
    let env = EvalEnv.insert_val_bare "result" l env in
    env, st, SContinue, VNull

  let eval_action_selector : extern = fun env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with
      | [(VRuntime{loc;obj_name}, _); _; _; _] -> loc, obj_name
      | _ -> failwith "unexpected args for action selector instantiation" in
    let selector = ActionSelector () in
    env, State.insert_extern loc selector st, SContinue, VRuntime{loc;obj_name}

  let eval_checksum16 : extern = fun env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with
      | [(VRuntime{loc;obj_name}, _); _; _; _] -> loc, obj_name
      | _ -> failwith "unexpected args for action selector instantiation" in
    let obj = Checksum16 () in
    env, State.insert_extern loc obj st, SContinue, VRuntime{loc;obj_name}      

  let eval_get : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VBit{w=Bigint.of_int 32; v=Bigint.zero}

  let eval_verify_checksum : extern = fun env st ts args ->
    let width = match ts with
      | _ :: o :: _ -> width_of_typ env o
      | _ -> failwith "unexpected type args for verify checksum" in
    let (condition, data, checksum, algo) = match args with
      | [(VBool condition,_); (VTuple data, _);
        (VBit{v;_}, _); (VEnumField{enum_name;_},_)] ->
        condition, data, v, enum_name
      | _ -> failwith "unexpected args for verify checksum" in
    if not condition then env, st, SContinue, VNull else
    let result = 
      data
      |> package_for_hash st
      |> Hash.hash algo
      |> adjust_hash_value Bigint.zero (Bitstring.power_of_two width) in
    if Bigint.(checksum = result) then env, st, SContinue, VNull
    else env, st, SReject "ChecksumError", VNull

  let eval_update_checksum : extern = fun env st ts args ->
    let width = match ts with
      | _ :: o :: _ -> width_of_typ env o
      | _ -> failwith "unexpected type args for verify checksum" in
    let (condition, data, checksum, algo) = match args with
      | [(VBool condition,_); (VTuple data, _);
        (VBit{v;_}, _); (VEnumField{enum_name;_},_)] ->
        condition, data, v, enum_name
      | _ -> failwith "unexpected args for verify checksum" in
    if not condition then env, st, SContinue, VNull else
    let result = 
      data
      |> package_for_hash st
      |> Hash.hash algo
      |> adjust_hash_value Bigint.zero (Bitstring.power_of_two width) in
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VBit{w=width;v=result}) st in
    let env' = EvalEnv.insert_val_bare "checksum" l env in
    env', st, SContinue, VNull

  let value_of_payload (st : state) : value = 
      st
      |> State.get_packet
      |> (fun x -> x.main)
      |> Cstruct.to_string
      |> String.to_list
      |> List.map ~f:Char.to_int
      |> List.map ~f:Bigint.of_int
      |> List.map ~f:(fun x -> Bigint.of_int 8, x)
      |> List.fold ~init:Bigint.(zero,zero) ~f:(fun (accw, accv) (nw, nv) ->
          Bigint.(accw + nw, Bitstring.shift_bitstring_left accv nw + nv))
      |> (fun (w,v) -> VBit { w; v })

  let eval_verify_checksum_with_payload : extern = fun env st ts args ->
    let width = match ts with
      | _ :: o :: _ -> width_of_typ env o
      | _ -> failwith "unexpected type args for verify checksum" in
    let (condition, data, checksum, algo) = match args with
      | [(VBool condition,_); (VTuple data, _);
        (VBit{v;_}, _); (VEnumField{enum_name;_},_)] ->
        condition, data, v, enum_name
      | _ -> failwith "unexpected args for verify checksum" in
    if not condition then env, st, SContinue, VNull else
    let payload_value = value_of_payload st in (* TODO *)
    let data = payload_value :: data in
    let result = 
      data
      |> package_for_hash st
      |> Hash.hash algo
      |> adjust_hash_value Bigint.zero (Bitstring.power_of_two width) in
    if Bigint.(checksum = result) then env, st, SContinue, VNull
    else env, st, SReject "ChecksumError", VNull

  let eval_update_checksum_with_payload : extern = fun env st ts args ->
    let width = match ts with
      | _ :: o :: _ -> width_of_typ env o
      | _ -> failwith "unexpected type args for verify checksum" in
    let (condition, data, checksum, algo) = match args with
      | [(VBool condition,_); (VTuple data, _);
        (VBit{v;_}, _); (VEnumField{enum_name;_},_)] ->
        condition, data, v, enum_name
      | _ -> failwith "unexpected args for verify checksum" in
    if not condition then env, st, SContinue, VNull else
    let payload_value = value_of_payload st in (* TODO *)
    let data = payload_value :: data in
    let result = 
      data
      |> package_for_hash st
      |> Hash.hash algo
      |> adjust_hash_value Bigint.zero (Bitstring.power_of_two width) in
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VBit{w=width;v=result}) st in
    let env' = EvalEnv.insert_val_bare "checksum" l env in
    env', st, SContinue, VNull

  let eval_resubmit : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VNull

  let eval_recirculate : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VNull

  let eval_clone : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VNull

  let eval_clone3 : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VNull

  let eval_truncate : extern = fun env st ts args ->
    (* TODO: actually implement *)
    env, st, SContinue, VNull

  let eval_assert : extern = fun env st ts args ->
    match args with
    | [(VBool true, _)] -> env, st, SContinue, VNull
    | [(VBool false,_)] -> v1_assert () (* TODO: provide an info.t *)
    | _ -> failwith "unexpected args for assert/assume"

  let eval_assume : extern = eval_assert

  let eval_log_msg : extern = fun env st ts args ->
    env, st, SContinue, VNull


  (* stp: this value is never actually used; I'm keeping it in to keep track
  of what is supported etc. *)
  let externs = [
    ("counter", eval_counter);
    ("count", eval_count); (* overloaded *)
    ("direct_counter", eval_direct_counter); (* unsupported *)
    ("meter", eval_meter); (* unsupported *)
    ("execute_meter", eval_execute_meter); (* unsupported *)
    ("direct_meter", eval_direct_meter); (* unsupported *)
    ("read", eval_read); (* overloaded*)
    ("register", eval_register);
    ("write", eval_write);
    ("action_profile", eval_action_profile); (* unsupported *)
    ("random", eval_random);
    ("digest", eval_digest); (* unsupported *)
    ("mark_to_drop", eval_mark_to_drop); (* overloaded, deprecated *)
    ("hash", eval_hash);
    ("action_selector", eval_action_selector); (* unsupported *)
    ("Checksum16", eval_checksum16); (* deprecated; unsupported *)
    ("get", eval_get); (* deprecated; unsupported *)
    ("verify_checksum", eval_verify_checksum);
    ("update_checksum", eval_update_checksum);
    ("verify_checksum_with_payload", eval_verify_checksum_with_payload);
    ("update_checksum_with_payload", eval_update_checksum_with_payload);
    ("resubmit", eval_resubmit); (* unsupported *)
    ("recirculate", eval_recirculate); (* unsupported *)
    ("clone", eval_clone); (* unsupported *)
    ("clone3", eval_clone3); (* unsupported *)
    ("truncate", eval_truncate); (* unsupported *)
    ("assert", eval_assert);
    ("assume", eval_assume);
    ("log_msg", eval_log_msg); (* overloaded; unsupported *)
  ]

  let eval_extern name =
    match name with
    | "counter" -> eval_counter
    | "count" -> eval_count
    | "direct_counter" -> eval_direct_counter
    | "meter" -> eval_meter
    | "read" -> eval_read
    | "register" -> eval_register
    | "write" -> eval_write
    | "action_profile" -> eval_action_profile
    | "random" -> eval_random
    | "digest" -> eval_digest
    | "mark_to_drop" -> eval_mark_to_drop
    | "hash" -> eval_hash
    | "action_selector" -> eval_action_selector
    | "Checksum16" -> eval_checksum16
    | "get" -> eval_get
    | "verify_checksum" -> eval_verify_checksum
    | "update_checksum" -> eval_update_checksum
    | "verify_checksum_with_payload" -> eval_verify_checksum_with_payload
    | "update_checksum_with_payload" -> eval_update_checksum_with_payload
    | "resubmit" -> eval_resubmit
    | "recirculate" -> eval_recirculate
    | "clone" -> eval_clone
    | "clone3" -> eval_clone3
    | "truncate" -> eval_truncate
    | "assert" -> eval_assert
    | "assume" -> eval_assume
    | "log_msg" -> eval_log_msg
    | _ -> failwith "unknown v1 extern"

  let initialize_metadata meta st =
    let nine = Bigint.of_int 9 in
    State.insert_heap
      "__INGRESS_PORT__"
      (VBit{w=nine; v=meta})
      st

  let check_pipeline env = () (* TODO: v1-dependent static analysis *)
    (** - checks that direct counters are associated with at most one table.
        - checks that direct meters are associated with at most one table.
        - checks that execute_meter T is a bit<W> type.
        - checks that the read meter T is a bit<W> type.
        - checks that the read register T is a bit<W> type.
        - checks that the write T is a bit<W> type.
        - checks that the random T is a bit<W> type.
        - checks all the constraints on the hash arg types.
        - checks all the constraints on the verify_checksum(_with_payload) arg types.
        - checks all the constraints on the update_checksum(_with_payload) arg types.
        - checks that verify and update checksum controls only do certain
          kinds of statements/expressions. *)

  let eval_v1control (ctrl : ctrl) (env : env) (app) (ctrl_name : string) (control : value)
      (args : Expression.t option list) (st : state) : state * signal =
    let env = EvalEnv.set_namespace ctrl_name env in
    let (st',s,_) = app ctrl env st SContinue control args in
    (st', s)

  let eval_pipeline
        (ctrl: ctrl)
        (env: env)
        (st: obj State.t)
        (pkt: pkt)
        (app: state apply) =
    let in_port = State.find_heap "__INGRESS_PORT__" st
      |> assert_bit |> snd in
    (* let fst (a,b,_) = (a,b) in *)
    let main = State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "main")) env) st in
    let vs = assert_package main |> snd in
    let parser =
      List.Assoc.find_exn vs "p"   ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let verify =
      List.Assoc.find_exn vs "vr"  ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let ingress =
      List.Assoc.find_exn vs "ig"  ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let egress =
      List.Assoc.find_exn vs "eg"  ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let compute =
      List.Assoc.find_exn vs "ck"  ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let deparser =
      List.Assoc.find_exn vs "dep" ~equal:String.equal
      |> fun x -> State.find_heap x st in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let vpkt = VRuntime { loc = State.packet_location; obj_name = "packet_in"; } in
    let hdr =
      init_val_of_typ env (List.nth_exn params 1).typ in
    let meta =
      init_val_of_typ env (List.nth_exn params 2).typ in
    let std_meta =
      init_val_of_typ env (List.nth_exn params 3).typ in
    let vpkt_loc, hdr_loc, meta_loc, std_meta_loc =
      State.fresh_loc (), State.fresh_loc (), State.fresh_loc (), State.fresh_loc () in
    let st = st
      |> State.insert_heap vpkt_loc vpkt
      |> State.insert_heap hdr_loc hdr
      |> State.insert_heap meta_loc meta
      |> State.insert_heap std_meta_loc std_meta in
    let env =
      EvalEnv.(env
              |> insert_val (BareName (Info.dummy, "packet"  )) vpkt_loc
              |> insert_val (BareName (Info.dummy, "hdr"     )) hdr_loc
              |> insert_val (BareName (Info.dummy, "meta"    )) meta_loc
              |> insert_val (BareName (Info.dummy, "std_meta")) std_meta_loc
              |> insert_typ (BareName (Info.dummy, "packet"  )) (List.nth_exn params 0).typ
              |> insert_typ (BareName (Info.dummy, "hdr"     )) (List.nth_exn params 1).typ
              |> insert_typ (BareName (Info.dummy, "meta"    )) (List.nth_exn params 2).typ
              |> insert_typ (BareName (Info.dummy, "std_meta")) (List.nth_exn params 3).typ) in
    (* TODO: implement a more responsible way to generate variable names *)
    let nine = Bigint.((one + one + one) * (one + one + one)) in
    let (st, _) = 
      assign_lvalue
        st
        env
        {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")};typ = (List.nth_exn params 3).typ}; 
                name="ingress_port"; }; typ = Bit {width = 9}}
        (VBit{w=nine;v=in_port})
        in
    let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "packet"))); dir = InOut; typ = (List.nth_exn params 0).typ}) in
    let hdr_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "hdr"))); dir = InOut; typ = (List.nth_exn params 1).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "meta"))); dir = InOut; typ = (List.nth_exn params 2).typ}) in
    let std_meta_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "std_meta"))); dir = InOut; typ = (List.nth_exn params 3).typ}) in
    let env = EvalEnv.set_namespace "p." env in
    let (st, state,_) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let env = EvalEnv.set_namespace "" env in
    let st =
      match state with 
      | SReject err -> 
        assign_lvalue st env
          {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")}; typ = (List.nth_exn params 3).typ;}; name="parser_error"}; typ = Error}
          (VError(err))
        |> fst
      | SContinue -> st
      | _ -> failwith "parser should not exit or return" in
    let vpkt' = VRuntime { loc = State.packet_location; obj_name = "packet_out"; } in
    let st = State.insert_heap vpkt_loc vpkt' st in
    let env = EvalEnv.insert_typ (BareName (Info.dummy, "packet")) (List.nth_exn deparse_params 0).typ env in
    let (st, s) = st
      |> eval_v1control ctrl env app "vr."  verify   [hdr_expr; meta_expr] in
    let st = 
      match s with
      | SReject "ChecksumError" ->
        assign_lvalue
          st
          env
          {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")};typ = (List.nth_exn params 3).typ}; 
                  name="checksum_error"; }; typ = Bit {width = 1}}
          (VBit{v=Bigint.one;w=Bigint.one}) |> fst
      | SContinue | SReturn _ | SExit | SReject _ -> st in
    let st = st
      |> eval_v1control ctrl env app "ig."  ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst in
    let struc = State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "std_meta")) env) st in
    let egress_spec_val = match struc with
      | VStruct {fields} ->
        List.Assoc.find_exn fields "egress_spec" ~equal:String.equal
      | _ -> failwith "std meta is not a struct after ingress" in
    if Bigint.(egress_spec_val |> bigint_of_val = drop_spec) then st, env, None else
    let st,_ = 
      assign_lvalue 
        st
        env
        {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")};typ = (List.nth_exn params 3).typ}; 
                name="egress_port"; }; typ = Bit {width = 9}}
        egress_spec_val
        in
    let st =
      st
      |> eval_v1control ctrl env app "eg."  egress   [hdr_expr; meta_expr; std_meta_expr] |> fst
      |> eval_v1control ctrl env app "ck."  compute  [hdr_expr; meta_expr] |> fst
      |> eval_v1control ctrl env app "dep." deparser [pkt_expr; hdr_expr] |> fst in
    st, env, Some (State.get_packet st)

  let get_outport (st : state) (env : env) : Bigint.t =
    match State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "std_meta")) env) st with
    | VStruct {fields;_} ->
      List.Assoc.find_exn fields "egress_port" ~equal:String.equal |> bigint_of_val
    | _ -> drop_spec

end

module V1Switch : Target = P4core.Corize(PreV1Switch)
