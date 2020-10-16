module I = Info
open Target
open Prog
open Env
open Value
open Core_kernel
open Typed
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

module PreUp4Filter : Target = struct

  (* TODO: Define uP4 obj *)
  type obj = 
    | Packet of {pck: int list; size: int} (* represented as a byte array *)
    (*
    | IM_T of {}  (* intrinsic metadata and constraints *)
    | emitter (* assemble packets *)
    | extractor (* header extraction *)
    | in_buf (* input buffer *)
    | out_buf (* output buffer *)
    *)

  type state = obj State.t

  type extern = state pre_extern

  (* TODO: Implement uP4 externs *)

  (* Create instances of pkt extern *)
  let eval_copy_from : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_length : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_set_out_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_in_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_out_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_value : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_drop : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_emit : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_extract : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_lookahead : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_dequeue : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_enqueue : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_to_in_buf : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_merge : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  (* stp: never actually used; see note in v1model.ml *)
  let externs = [
    ("copy_from", eval_copy_from); (* Overloaded. input type is pkt or im_t *)
    ("get_length", eval_get_length);
    ("set_out_port", eval_set_out_port);
    ("get_in_port", eval_get_in_port); 
    ("get_out_port", eval_get_out_port);
    ("get_value", eval_get_value);
    ("drop", eval_drop);
    ("emit", eval_emit);
    ("extract", eval_extract);
    ("lookahead", eval_lookahead);
    ("dequeue", eval_dequeue);
    ("enqueue", eval_enqueue); 
    ("to_in_buf", eval_to_in_buf);
    ("merge", eval_merge);
  ]

  let read_header_field : obj reader = fun is_valid fields fname ->
    List.Assoc.find_exn fields fname ~equal:String.equal

  let write_header_field : obj writer = fun is_valid fields fname fvalue ->
    let fs = List.map fields
      ~f:(fun (n,v) -> if String.equal n fname then n, fvalue else n,v) in
    VHeader {fields = fs; is_valid; }

  let assign_lvalue = assign_lvalue read_header_field write_header_field

  let eval_extern name =
    match name with
    | "copy_from" -> eval_copy_from (* Overloaded. input type is pkt or im_t *)
    | "get_length" -> eval_get_length
    | "set_out_port" -> eval_set_out_port
    | "get_in_port" -> eval_get_in_port 
    | "get_out_port" -> eval_get_out_port
    | "get_value" -> eval_get_value
    | "drop" -> eval_drop
    | "emit" -> eval_emit
    | "extract" -> eval_extract
    | "lookahead" -> eval_lookahead
    | "dequeue" -> eval_dequeue
    | "enqueue" -> eval_enqueue 
    | "to_in_buf" -> eval_to_in_buf
    | "merge" -> eval_merge
    | _ -> failwith "extern unknown in up4 or not yet implemented"

  let initialize_metadata meta st =
    State.insert_heap "__INGRESS_PORT__" (VInteger meta) st

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
  (env,st) : state * signal =
    let (st,s,_) = app ctrl env st SContinue control args in 
    (st,s)

  let eval_pipeline (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (app : state apply) : state * env * pkt option =
    let main = State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "main")) env) st in
    let vs = assert_package main |> snd in
    let parser = List.Assoc.find_exn vs "prs"  ~equal:String.equal |> fun x -> State.find_heap x st in
    let filter = List.Assoc.find_exn vs "filt" ~equal:String.equal |> fun x -> State.find_heap x st in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let vpkt = VRuntime {loc = State.packet_location; obj_name = "packet_in"; } in
    let pkt_name = Types.BareName (Info.dummy, "packet") in
    let hdr = init_val_of_typ env (List.nth_exn params 1).typ in
    let hdr_name = Types.BareName (Info.dummy, "headers") in
    let accept = VBool (false) in
    let accept_name = Types.BareName (Info.dummy, "accept") in
    let vpkt_loc, hdr_loc, accept_loc = 
      State.fresh_loc (), State.fresh_loc (), State.fresh_loc () in
    let st = st
      |> State.insert_heap vpkt_loc vpkt
      |> State.insert_heap hdr_loc hdr
      |> State.insert_heap accept_loc accept in
    let env =
      EvalEnv.(env
              |> insert_val pkt_name    vpkt_loc
              |> insert_val hdr_name    hdr_loc
              |> insert_val accept_name accept_loc
              |> insert_typ pkt_name    (List.nth_exn params 0).typ
              |> insert_typ hdr_name    (List.nth_exn params 1).typ
              |> insert_typ accept_name Type.Bool) in
    let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = Name pkt_name; dir = InOut; typ = (List.nth_exn params 0).typ}) in
    let hdr_expr =
      Some (Info.dummy, {expr = Name hdr_name; dir = InOut; typ = (List.nth_exn params 1).typ}) in
    let accept_expr =
      Some (Info.dummy, {expr = Name accept_name; dir = InOut; typ = Bool}) in
    let (st,state, _) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr] in
    match state with 
    | SReject _ -> 
      let (st, _) =
        assign_lvalue
          st
          env
          {lvalue = LName {name = accept_name}; typ = Bool}
          (VBool(false)) in
      st, env, None
    | SContinue | SExit | SReturn _ ->
      let (st,_) = 
        eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app (env, st) in
      st, env, 
      if State.find_heap (EvalEnv.find_val accept_name env) st |> assert_bool
      then Some pkt else None

  let get_outport (st : state) (env : env) : Bigint.t =
    State.find_heap "__INGRESS_PORT__" st |> bigint_of_val
  
end

module Up4Filter : Target = P4core.Corize(PreUp4Filter)
