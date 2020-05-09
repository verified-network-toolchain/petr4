open Typed
open Prog
open Value
open Env
open Target
module I = Info
open Core_kernel
module Info = I


module PreV1Switch : Target = struct
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
        states: Value.value list;
        size: Bigint.t;
      }
    | ActionProfile of unit

  and counter_type =
    | Packets of Bigint.t list
    | Bytes of Bigint.t list
    (* packet count, byte count *)
    | Both of (Bigint.t * Bigint.t) list

  type state = obj State.t
  type extern = state pre_extern

  let eval_counter : extern = fun ctrl env st ts args ->
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
    env, State.insert loc ctr st, SContinue, VRuntime {loc = loc; obj_name = "counter"}
      
  let eval_count_counter : extern = fun ctrl env st ts args ->
    let (loc, v) = match args with
      | [(VRuntime{loc;_},_); (VBit {v;_}, _)] -> loc, Bigint.to_int_exn v
      | _ -> failwith "unexpected args for count counter" in
    let pkt_len = (State.get_packet st).in_size |> Bigint.of_int in
    let ctr = State.find loc st in
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
    env, State.insert loc ctr' st, SContinue, VNull

  let eval_count_direct_counter : extern = fun ctrl env st ts args ->
    (* actual direct counting implemented in target-dependent table execution *)
    env, st, SContinue, VNull

  let eval_count : extern = fun ctrl env st ts args ->
    match args with 
    | [_;_] -> eval_count_counter ctrl env st ts args
    | [_;] -> eval_count_direct_counter ctrl env st ts args
    | _ -> failwith "unexpected args for count"

  let eval_direct_counter : extern = fun ctrl env st ts args ->
    match args with
    | [(VRuntime{loc;obj_name}, _); (VEnumField{enum_name;_}, _);] ->
      let dctr = match enum_name with
        | "packets" -> DirectCounter {typ = Packets []}
        | "bytes" -> DirectCounter {typ = Bytes []}
        | "packets_and_bytes" -> DirectCounter {typ = Both []}
        | _ -> failwith "unexpected field name for counter type" in
      env, State.insert loc dctr st, SContinue, VRuntime{loc;obj_name}
    | _ -> failwith "unexpected args for direct counter"

  let eval_meter : extern = fun ctrl env st ts args ->
    (* TODO: current implementation is trivial *)
    let (loc, obj_name) = match args with
      | [(VRuntime{loc;obj_name},_); _; _] -> loc, obj_name
      | _ -> failwith "unexpected args for meter" in
    let meter = Meter () in
    env, State.insert loc meter st, SContinue, VRuntime{loc;obj_name}

  let eval_execute_meter : extern = fun ctrl env st ts args ->
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_direct_meter : extern = fun ctrl env st ts args ->
    ignore (DirectMeter ());
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_register_read : extern = fun _ env st _ args ->
    match args with
    | [(VRuntime {loc;_}, _); (_,t) ; (VBit {w = w; v = v}, _)] ->
      let reg_obj = State.find loc st in
      let states = match reg_obj with
        | Register {states; _} -> states
        | _ -> failwith "Reading from an object other than a v1 register" in
      let read_val =
        Bigint.to_int_exn v
        |> List.nth states 
        |> Option.value ~default:(init_val_of_typ env t) in
      let env'= EvalEnv.insert_val (Types.BareName (Info.dummy, "result")) read_val env in 
      env', st, SContinue, read_val
    | _ -> failwith "unexpected args for register read"
  
  let eval_meter_read : extern = fun ctrl env st ts args ->
    env, st, SContinue, VNull (* TODO: actually implement *)

  let eval_read : extern = fun ctrl env st ts args ->
    match args with 
    | [ _; _; _] -> eval_register_read ctrl env st ts args
    | [ _; _;] -> eval_meter_read ctrl env st ts args
    | _ -> failwith "unexpected read args"
    
  let eval_register : extern = fun _ env st typs args ->
    let typ = match typs with
      | [t] -> t
      | _ -> failwith "unexpected typ args for register" in
    match args with
    | [(VRuntime {loc;obj_name}, _); (VBit {w = _; v = size}, _)] ->
      let init_val = init_val_of_typ env typ in
      let states = List.init (Bigint.to_int_exn size) ~f:(fun _ -> init_val) in 
      let reg = Register {states = states;
                          size = size; } in
      let st' = State.insert loc reg st in
      env, st', SContinue, VRuntime {loc = loc; obj_name = obj_name}
    | _ -> failwith "unexpected args for register instantiation"

  let eval_write : extern = fun _ env st _ args -> 
    match args with
    | [(VRuntime {loc;_}, _); 
        (VBit {w = _; v = v_index}, _) ; 
        (write_val, _)] ->
      let reg_obj = State.find loc st in
      let states, size = match reg_obj with
        | Register {states; size} -> states, size
        | _ -> failwith "Reading from an object other than a v1 register" in
      let subs_f = fun i x -> 
        if Bigint.(of_int i = v_index) then write_val else x in 
      let states' = List.mapi ~f:subs_f states in
      let reg' = Register {states = states';
                            size = size;} in
      let st' = State.insert loc reg' st in
      env, st', SContinue, write_val 
    | _ -> failwith "unexpected args for register write"

  let eval_action_profile : extern = fun ctrl env st ts args ->
    let (loc, obj_name) = match args with 
      | [(VRuntime{loc;obj_name},_); _] -> loc, obj_name
      | _ -> failwith "unexpected args for action profile" in
    let prof = ActionProfile () in
    env, State.insert loc prof st, SContinue, VRuntime{loc;obj_name}

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

  let externs = [
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
  let eval_extern name ctrl env st targs args =
    let extern =
      match name with
      | "register" -> eval_register
      | "read" -> eval_read
      | "write" -> eval_write
      | "counter" -> eval_counter
      | "count" -> eval_count
      | _ -> failwith "TODO: v1 extern unimplemented" in
    extern ctrl env st targs args

  let initialize_metadata meta env =
    let nine = Bigint.of_int 9 in
    EvalEnv.insert_val
      (BareName (Info.dummy, "ingress_port"))
      (VBit{w=nine; v=meta})
      env

  let check_pipeline env = () (* TODO: v1-dependent static analysis *)
    (** - checks that direct counters are associated with at most one table.
        - checks that direct meters are associated with at most one table. 
        - checks that verify and update checksum controls only do certain
          kinds of statements/expressions.
        -  *)

  let eval_v1control (ctrl : ctrl) (app) (ctrl_name : string) (control : value)
      (args : Expression.t option list) (env,st) : env * state * signal =
    let env = EvalEnv.set_namespace ctrl_name env in
    let (env,st',s,_) = app ctrl env st SContinue control args in
    (EvalEnv.set_namespace "" env, st', s)

  let eval_pipeline
        (ctrl: ctrl)
        (env: env)
        (st: obj State.t)
        (pkt: pkt)
        (app: state apply) =
    let in_port = EvalEnv.find_val (BareName (Info.dummy, "ingress_port")) env
      |> assert_bit |> snd in 
    let fst23 (a,b,_) = (a,b) in  
    let main = EvalEnv.find_val (BareName (Info.dummy, "main")) env in
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
    let vpkt = VRuntime { loc = State.packet_location; obj_name = "packet_in"; } in
    let hdr =
      init_val_of_typ env (snd (List.nth_exn params 1)).typ in
    let meta =
      init_val_of_typ env (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init_val_of_typ env (snd (List.nth_exn params 3)).typ in
    let env =
      EvalEnv.(env
              |> insert_val (BareName (Info.dummy, "packet"  )) vpkt
              |> insert_val (BareName (Info.dummy, "hdr"     )) hdr
              |> insert_val (BareName (Info.dummy, "meta"    )) meta
              |> insert_val (BareName (Info.dummy, "std_meta")) std_meta
              |> insert_typ (BareName (Info.dummy, "packet"  )) (snd (List.nth_exn params 0)).typ
              |> insert_typ (BareName (Info.dummy, "hdr"     )) (snd (List.nth_exn params 1)).typ
              |> insert_typ (BareName (Info.dummy, "meta"    )) (snd (List.nth_exn params 2)).typ
              |> insert_typ (BareName (Info.dummy, "std_meta")) (snd (List.nth_exn params 3)).typ) in
    (* TODO: implement a more responsible way to generate variable names *)
    let nine = Bigint.((one + one + one) * (one + one + one)) in
    let (env, _) = 
      assign_lvalue 
        env
        {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")};typ = (snd (List.nth_exn params 3)).typ}; 
                name="ingress_port"; }; typ = Bit {width = 9}}
        (VBit{w=nine;v=in_port}) in
    let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "packet"))); dir = InOut; typ = (snd (List.nth_exn params 0)).typ}) in
    let hdr_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "hdr"))); dir = InOut; typ = (snd (List.nth_exn params 1)).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "meta"))); dir = InOut; typ = (snd (List.nth_exn params 2)).typ}) in
    let std_meta_expr =
      Some (Info.dummy, {expr = (Name (BareName (Info.dummy, "std_meta"))); dir = InOut; typ = (snd (List.nth_exn params 3)).typ}) in
    let env = EvalEnv.set_namespace "p." env in
    let (env, st, state,_) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let env = EvalEnv.set_namespace "" env in
    let (env,st) =
      match state with 
      | SReject err -> 
        assign_lvalue env {lvalue = LMember{expr={lvalue = LName{name = Types.BareName (Info.dummy, "std_meta")}; typ = (snd (List.nth_exn params 3)).typ;}; name="parser_error"}; typ = Error} (VError(err))
        |> fst, st
      | SContinue -> (env,st)
      | _ -> failwith "parser should not exit or return" in
    let vpkt' = VRuntime { loc = State.packet_location; obj_name = "packet_out"; } in
    let env = EvalEnv.insert_val (BareName (Info.dummy, "packet")) vpkt' env in
    let env = EvalEnv.insert_typ (BareName (Info.dummy, "packet")) (snd (List.nth_exn deparse_params 0)).typ env in
    let (env,st,_) = 
      (env,st)
      |> eval_v1control ctrl app "vr."  verify   [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app "ig."  ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app "eg."  egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app "ck."  compute  [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app "dep." deparser [pkt_expr; hdr_expr] in
    st, env, State.get_packet st

end

module V1Switch : Target = P4core.Corize(PreV1Switch)