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

  (* let dummy = Packet {pck = []; size = 0} maybe we need this?*)

  type state = obj State.t

  type extern = state pre_extern

  (* TODO: Implement uP4 externs *)

  (* Create instances of pkt extern *)
  let eval_copy_from : extern = fun env st ts args -> 
    let (loc, copy_loc) = match args with 
      | [(VRuntime {loc = l; _}, _);
         (VRuntime{loc = c_loc; _}, _)] -> l, c_loc
      | _ -> failwith "unexpected args for packet copying" in
    let pck = Packet { pck = []; size = 0} in
    env, State.insert_extern loc pck st, SContinue, VRuntime {loc = loc; obj_name = "packet_copy"}

  let eval_get_length : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_set_out_port : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_get_in_port : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_get_out_port : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_get_value : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_drop : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_dequeue : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_enqueue : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_to_in_buf : extern = fun env st ts args -> 
    failwith "unimplemented"

  let eval_merge : extern = fun env st ts args -> 
    failwith "unimplemented"

  (* stp: never actually used; see note in v1model.ml *)
  let externs = [
    ("copy_from", eval_copy_from); (* Overloaded. input type is pkt or im_t *)
    ("get_length", eval_get_length);
    ("set_out_port", eval_set_out_port);
    ("get_in_port", eval_get_in_port); 
    ("get_out_port", eval_get_out_port);
    ("get_value", eval_get_value);
    ("drop", eval_drop);
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
    (* | "copy_from" -> eval_copy_from (* Overloaded. input type is pkt or im_t *)
       | "get_length" -> eval_get_length
       | "set_out_port" -> eval_set_out_port
       | "get_in_port" -> eval_get_in_port 
       | "get_out_port" -> eval_get_out_port
       | "get_value" -> eval_get_value
       | "drop" -> eval_drop
       | "dequeue" -> eval_dequeue
       | "enqueue" -> eval_enqueue 
       | "to_in_buf" -> eval_to_in_buf
       | "merge" -> eval_merge *)
    | _ -> failwith "extern unknown in up4 or not yet implemented"

  (* TODO: below is copied from ebpf.ml. Check if it's okay *)
  let initialize_metadata meta st =
    State.insert_heap "__INGRESS_PORT__" (VInteger meta) st

  let check_pipeline env = failwith "unimplemented"

  (* TODO: below is copied from ebpf.ml. Check if it's okay *)
  let eval_up4_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
      (env,st) : state * signal =
    let (st,s,_) = app ctrl env st SContinue control args in 
    (st,s)

  let helper (param_string : loc) (param_type : Type.t) (env : env) (st : state)
    : value * Types.name * loc * state * env =
    let param_value = init_val_of_typ env param_type in 
    let param_name = Types.BareName (Info.dummy, param_string) in
    let param_loc = State.fresh_loc () in 
    let st = State.insert_heap param_loc param_value st in 
    let env = EvalEnv.insert_val param_name param_loc env in
    let env = EvalEnv.insert_typ param_name param_type env in
    param_value, param_name, param_loc, st, env

  (* Push [pkt] through pipeline of this architecture, 
     updating the environment and state and return the 
     new state, environment and the packet if it was accepted! *)
  let eval_pipeline (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (app : state apply) : state * env * pkt option =
    (* Get main *)
    let main = State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "main")) env) st in
    (* Get arguments passed into main *)
    let vs = assert_package main |> snd in
    (* Get Package parameters *)
    let parser = List.Assoc.find_exn vs "p" ~equal:String.equal |> fun x -> State.find_heap x st in
    let control = List.Assoc.find_exn vs "c" ~equal:String.equal |> fun x -> State.find_heap x st in
    let deparser = List.Assoc.find_exn vs "d" ~equal:String.equal |> fun x -> State.find_heap x st in
    (* Parser params *)
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    (* Micro Control params *)
    let control_params = 
      match control with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "control is not a control object" in 
    (* Deparser params *)
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let vpkt, pkt_name, vpkt_loc = VRuntime {loc = State.packet_location; obj_name = "packet_in"; }, 
                                   Types.BareName (Info.dummy, "packet"),
                                   State.fresh_loc() in 
    let im, im_name, im_loc = VRuntime {loc = State.im_t_location; obj_name = "im_t"; }, 
                              Types.BareName (Info.dummy, "im"),
                              State.fresh_loc() in
    let st = st
             |> State.insert_heap vpkt_loc vpkt
             |> State.insert_heap im_loc im in 
    let env =
      EvalEnv.(env
               |> insert_val pkt_name vpkt_loc
               |> insert_val im_name  im_loc
               |> insert_typ pkt_name (List.nth_exn params 0).typ
               |> insert_typ im_name  (List.nth_exn params 1).typ) in
    let hdrs, hdrs_name, hdrs_loc, st, env = 
      helper "hdrs" (List.nth_exn params 2).typ env st in
    let meta, meta_name, meta_loc, st, env = 
      helper "meta" (List.nth_exn params 3).typ env st in
    let in_p, in_p_name, in_p_loc, st, env = 
      helper "in_param" (List.nth_exn params 4).typ env st in
    let inout_p, inout_p_name, inout_p_loc, st, env = 
      helper "inout_param" (List.nth_exn params 5).typ env st in
    let out_p, out_p_name, out_p_loc, st, env = 
      helper "out_param" (List.nth_exn control_params 3).typ env st in
    let open Expression in
    let pkt_expr = (* TODO: double check. packet does not have direction in spec. *)
      Some (Info.dummy, {expr = Name pkt_name; dir = InOut; typ = (List.nth_exn params 0).typ}) in
    let im_expr = (* TODO: Are we doing this right? (Direction) *)
      Some (Info.dummy, {expr = Name im_name; dir = Directionless; typ = (List.nth_exn params 1).typ}) in
    let hdrs_expr =
      Some (Info.dummy, {expr = Name hdrs_name; dir = Out; typ = (List.nth_exn params 2).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = Name meta_name; dir = InOut; typ = (List.nth_exn params 3).typ}) in
    let in_expr =
      Some (Info.dummy, {expr = Name in_p_name; dir = In; typ = (List.nth_exn params 4).typ}) in
    let inout_expr =
      Some (Info.dummy, {expr = Name inout_p_name; dir = InOut; typ = (List.nth_exn params 5).typ}) in
    let out_expr = 
      Some (Info.dummy, {expr = Name out_p_name; dir = Out; typ = (List.nth_exn control_params 4).typ}) in
    (* Go through micro parser *)
    let (st,signal, _) =
      app ctrl env st SContinue parser [pkt_expr; im_expr; hdrs_expr; meta_expr; in_expr; inout_expr] in
    match signal with 
    | SReject _ -> st, env, None
    | SContinue | SExit | SReturn _ -> 
      (* Go through micro control *)
      let (st, signal) = eval_up4_ctrl ctrl control 
          [im_expr; hdrs_expr; meta_expr; 
           in_expr; out_expr; inout_expr] 
          app (env, st) in
      match signal with
      | SReject _ -> st, env, None
      | SContinue | SExit | SReturn _ -> 
        let vpkt' = VRuntime { loc = State.packet_location; obj_name = "packet_out"; } in
        let st = State.insert_heap vpkt_loc vpkt' st in
        let env = EvalEnv.insert_typ (BareName (Info.dummy, "packet")) 
            (List.nth_exn deparse_params 0).typ 
            env in
        (* Go through micro deparser *)
        let (st, signal) = eval_up4_ctrl ctrl deparser
            [pkt_expr; hdrs_expr] 
            app (env, st) in 
        match signal with
        | SReject _ -> st, env, None
        | SContinue | SExit | SReturn _ -> st, env, Some (State.get_packet st)


  (* TODO: below is copied from ebpf.ml. Check if it's okay *)
  let get_outport (st : state) (env : env) : Bigint.t =
    State.find_heap "__INGRESS_PORT__" st |> bigint_of_val

end 

module Up4Filter : Target = P4core.Corize(PreUp4Filter)
