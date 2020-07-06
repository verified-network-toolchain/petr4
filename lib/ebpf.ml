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

  type obj =
    | CounterArray of Bigint.t list
    | ArrayTable of unit (* TODO *)
    | HashTable of unit (* TODO *)

  let y = ArrayTable ()

  let z = HashTable ()

  type state = obj State.t

  type extern = state pre_extern

  let eval_counter_array : extern = fun env st ts args ->
    let loc, max_idx = match args with
      | [(VRuntime {loc;_}, _); (VBit{v;_},_);_] -> loc,v
      | _ -> failwith "unexpected counter array init args" in
    let init = Bigint.zero in
    let arr = List.init (max_idx |> Bigint.to_int_exn) ~f:(fun _ -> init) in
    let ctr = CounterArray arr in
    env,
    State.insert_extern loc ctr st,
    SContinue,
    VRuntime {loc = loc; obj_name = "CounterArray"}

  let eval_increment : extern = fun env st ts args ->
    let loc, v = match args with
      | [(VRuntime{loc;_}, _); (VBit{v;_},_)] -> loc, Bigint.to_int_exn v
      | _ -> failwith "unexpected counter array increment args" in
    let ctr = State.find_extern loc st in
    match ctr with
    | CounterArray vs ->
      let ctr' = CounterArray 
        (List.mapi vs
          ~f:(fun i elt -> if Int.(i = v) then Bigint.(elt + one) else elt)) in
      env, State.insert_extern loc ctr' st, SContinue, VNull
    | _ -> failwith "extern is not a counter array"

  let eval_add : extern = fun env st ts args ->
    let loc, idx, v = match args with
      | [(VRuntime{loc;_}, _); (VBit{v=idx;_}, _); (VBit{v;_}, _)] ->
        loc, Bigint.to_int_exn idx, v
      | _ -> failwith "unexpected counter array add args" in
    let ctr = State.find_extern loc st in
    match ctr with
    | CounterArray vs ->
      let ctr' = CounterArray
        (List.mapi vs
          ~f:(fun i elt -> if Int.(i = idx) then Bigint.(elt + v) else elt)) in
      env, State.insert_extern loc ctr' st, SContinue, VNull
    | _ -> failwith "extern is not a counter array"

  let eval_array_table : extern = fun env st _ args ->
    (* TODO: actually implement*)
    let loc = match args with
      | [(VRuntime {loc;_}, _); _] -> loc
      | _ -> failwith "unexpected array table init args" in
    env, State.insert_extern loc (ArrayTable ()) st,
    SContinue, VRuntime {loc;obj_name = "array_table"}

  let eval_hash_table : extern = fun env st _ args ->
    (* TODO: actually implement*)
    let loc = match args with
      | [(VRuntime {loc;_}, _); _] -> loc
      | _ -> failwith "unexpected array table init args" in
    env, State.insert_extern loc (HashTable ()) st,
    SContinue, VRuntime {loc;obj_name = "hash_table"}

  (* stp: never actually used; see note in v1model.ml *)
  let externs = [
    ("CounterArray", eval_counter_array);
    ("increment", eval_increment);
    ("add", eval_add);
    ("array_table", eval_array_table); (* unsupported *)
    ("hash_table", eval_hash_table); (* unsupported *)
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
    | "CounterArray" -> eval_counter_array
    | "increment" -> eval_increment
    | "add" -> eval_add
    | "array_table" -> eval_array_table
    | "hash_table" -> eval_hash_table
    | _ -> failwith "extern unknown in ebpf"

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

module EbpfFilter : Target = P4core.Corize(PreEbpfFilter)
