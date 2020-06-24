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

module PreEbpfFilter : Target = struct

  type obj = unit (* TODO *)

  type state = obj State.t

  type extern = state pre_extern

  let externs = []

  let read_header_field : obj reader = fun is_valid fields fname ->
    List.Assoc.find_exn fields fname ~equal:String.equal

  let write_header_field : obj writer = fun is_valid fields fname fvalue ->
    let fs = List.map fields
      ~f:(fun (n,v) -> if String.equal n fname then n, fvalue else n,v) in
    VHeader {fields = fs; is_valid; }

  let assign_lvalue = assign_lvalue read_header_field write_header_field

  let eval_extern _ = failwith ""

  let initialize_metadata meta env =
    env

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
  (env,st) : env * state * signal =
    let (env,st,s,_) = app ctrl env st SContinue control args in 
    (env,st,s)

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
    let (env, st,state, _) =
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
      let (env,st,_) = 
        eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app (env, st) in
      st, env, 
      if State.find_heap (EvalEnv.find_val accept_name env) st |> assert_bool
      then Some (State.get_packet st) else None

end

module EbpfFilter : Target = P4core.Corize(PreEbpfFilter)
