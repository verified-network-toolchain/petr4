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

  (* Copied from v1model *)
  let drop_spec = Bigint.of_int 511 

  let im_t_location = "__IM_T__" 

  type obj = 
    | Im_t of {out_port: Bigint.t; 
               in_port: Bigint.t; 
               queue_depth_at_dequeue: Bigint.t}  

  (* (* Unsupported externs *)
    | Packet (* represented as a byte array *)
    | emitter (* assemble packets *)
    | extractor (* header extraction *)
    | in_buf (* input buffer *)
    | out_buf (* output buffer *)
    *)

  type state = obj State.t

  type extern = state pre_extern

  (* Set out_port field to input to this extern function in the Im_t extern object. *)
  let eval_set_out_port : extern = fun env st ts args -> 
    let (loc, v) = match args with 
      | [(VRuntime {loc = l; _}, _);
         (VBit {v;_}, _)] -> l, v
      | _ -> failwith "unexpected args for set_out_port" in
    let im_t_obj = State.find_extern loc st in
    let in_port, queue_depth_at_dequeue = match im_t_obj with 
      | Im_t {in_port = i; queue_depth_at_dequeue = q; _} -> i, q in
    let new_im_t_obj = Im_t {out_port = v; in_port; queue_depth_at_dequeue} in
    env, State.insert_extern loc new_im_t_obj st, SContinue, VNull

  (* Get in_port field from the Im_t extern object. *)
  let eval_get_in_port : extern = fun env st ts args -> 
    let loc = match args with
      | [(VRuntime {loc = l; _}, _)] -> l
      | _ -> failwith "unexpected args for get_in_port" in
    let im_t_obj = State.find_extern loc st in
    let in_port, queue_depth_at_dequeue = match im_t_obj with
      | Im_t {in_port = i; queue_depth_at_dequeue = q; _} -> i, q in 
    env, st, SContinue, VBit {w = Bigint.of_int 9; v = in_port}

  (* Get out_port field from the Im_t extern object. *)
  let eval_get_out_port : extern = fun env st ts args -> 
    let loc = match args with
      | [(VRuntime {loc = l; _}, _);] -> l
      | _ -> failwith "unexpected args for get_out_port" in
    let im_t_obj = State.find_extern loc st in
    let out_port = match im_t_obj with
      | Im_t {out_port = o; _} -> o in 
    env, st, SContinue, VBit {w = Bigint.of_int 9; v = out_port}

  (* Get metadata_fields_t enum value from the Im_t extern object. *)
  let eval_get_value : extern = fun env st ts args -> 
    let loc, enum_name = match args with
      | [(VRuntime {loc = l; _}, _);
         (VEnumField{enum_name; _}, _)] -> l, enum_name
      | _ -> failwith "unexpected args for get_value" in
    let im_t_obj = State.find_extern loc st in
    let v = match enum_name, im_t_obj with
      | "QUEUE_DEPTH_AT_DEQUEUE", Im_t {queue_depth_at_dequeue = q; _} -> q 
      | s, _ -> failwith ("Unsupported metadata_fields_t: " ^ s) in 
    env, st, SContinue, VBit {w = Bigint.of_int 32; v = v}

  (* Set out_port field of the Im_t extern object to be the drop_spec. *)
  let eval_drop : extern = fun env st ts args -> 
    let loc = match args with 
      | [(VRuntime {loc = l; _}, _)] -> l
      | _ -> failwith "unexpected args for drop()" in
    let im_t_obj = State.find_extern loc st in
    let in_port, queue_depth_at_dequeue = match im_t_obj with 
      | Im_t {in_port = i; queue_depth_at_dequeue = q; _} -> i, q in
    let new_im_t_obj = Im_t {out_port = drop_spec; in_port; queue_depth_at_dequeue} in
    env, State.insert_extern loc new_im_t_obj st, SContinue, VNull

  let read_header_field : obj reader = fun is_valid fields fname ->
    List.Assoc.find_exn fields fname ~equal:String.equal

  let write_header_field : obj writer = fun is_valid fields fname fvalue ->
    let fields = List.map fields
        ~f:(fun (n, v) -> if String.equal n fname then n, fvalue else n, v) in
    VHeader {fields; is_valid}

  let assign_lvalue = assign_lvalue read_header_field write_header_field

  (* copy_from extern function of im_t extern is not supported *)
  let eval_extern name =
    match name with
    | "set_out_port" -> eval_set_out_port
    | "get_in_port" -> eval_get_in_port 
    | "get_out_port" -> eval_get_out_port
    | "get_value" -> eval_get_value
    | "drop" -> eval_drop
    | _ -> failwith "extern unknown in up4 or not yet implemented"

  (* Use the port number [meta] to set out_port and in_port of Im_t extern object. *)
  (* QUEUE_DEPTH_AT_DEQUEUE metadata hard coded.. it says in the up4 spec that 
     metadata_fileds_t enums are immutable intrinsic metadata field for the target. *)
  let initialize_metadata meta st =
    State.insert_extern im_t_location (
      Im_t {out_port = meta; in_port = meta; queue_depth_at_dequeue = Bigint.of_int 32}) st

  let check_pipeline env = failwith "unimplemented"

  (* below is copied from ebpf.ml *)
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
    let params = (assert_parser parser).pparams in
    (* Micro Control params *)
    let control_params = (assert_control control).cparams in 
    (* Deparser params *)
    let deparse_params = (assert_control deparser).cparams in 
    ignore deparse_params;
    let vpkt, pkt_name, vpkt_loc = VRuntime {loc = State.packet_location; obj_name = "packet_in"; }, 
                                   Types.BareName (Info.dummy, "packet"),
                                   State.fresh_loc() in 
    let im, im_name, im_loc = VRuntime {loc = im_t_location; obj_name = "im_t"; }, 
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
    let pkt_expr = 
      Some (Info.dummy, {expr = Name pkt_name; dir = Directionless; typ = (List.nth_exn params 0).typ}) in
    let im_expr = 
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
        let im_t = State.find_extern im_t_location st in 
        let outport = match im_t with 
          | Im_t {out_port; _} -> out_port in 
        if outport = drop_spec 
          then st, env, None
        else
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

  (* Get out_port field from the Im_t extern object. *)
  let get_outport (st : state) (env : env) : Bigint.t =
    match State.find_extern im_t_location st with
    | Im_t {out_port = out; _} -> out

end 

module Up4Filter : Target = P4core.Corize(PreUp4Filter)
