module I = Info
open Target
open Typed
open Prog
open Value
open Env
open Core_kernel
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

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
    ("direct_counter", eval_direct_counter); (* low priority *)
    ("meter", eval_meter);
    ("execute_meter", eval_execute_meter);
    ("direct_meter", eval_direct_meter); (* low priority *)
    ("read", eval_read); (* overloaded*)
    ("register", eval_register);
    ("write", eval_write);
    ("action_profile", eval_action_profile); (* low priority *)
    ("random", eval_random);
    ("digest", eval_digest);
    ("mark_to_drop", eval_mark_to_drop); (* overloaded, deprecated *)
    ("hash", eval_hash);
    ("action_selector", eval_action_selector); (* low priority *)
    ("Checksum16", eval_checksum16); (* deprecated *)
    ("get", eval_get); (* deprecated *)
    ("verify_checksum", eval_verify_checksum);
    ("update_checksum", eval_update_checksum);
    ("verify_checksum_with_payload", eval_verify_checksum_with_payload);
    ("update_checksum_with_payload", eval_update_checksum_with_payload);
    ("resubmit", eval_resubmit); (* on demand from benchmark suite *)
    ("recirculate", eval_recirculate); (* on demand from benchmark suite *)
    ("clone", eval_clone); (* on demand from benchmark suite *)
    ("clone3", eval_clone3); (* on demand from benchmark suite *)
    ("truncate", eval_truncate);
    ("assert", eval_assert);
    ("assume", eval_assume);
    ("log_msg", eval_log_msg); (* overloaded *)
  ]

  let corize_st (st : state) : Core.state =
    st
    |> State.filter ~f:(fun (_, o) -> is_core o)
    |> State.map ~f:(fun o -> assert_core o)

  let targetize_st (st : Core.state) : state = 
    State.map ~f:(fun o -> CoreObject o) st

  let targetize (ext : Core.extern) : extern =
    fun ctrl env st ts vs ->
    let (env', st', s, v) =
      ext ctrl env (corize_st st) ts vs in
    env', State.merge (targetize_st st') st, s, v

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
    EvalEnv.insert_val_bare "ingress_port" (VBit{w=nine; v=meta}) env

  let check_pipeline env = ()

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
    let pkt_name = Types.BareName (Info.dummy, "packet") in
    let hdr_name = Types.BareName (Info.dummy, "hdr") in
    let meta_name = Types.BareName (Info.dummy, "meta") in
    let std_meta_name = Types.BareName (Info.dummy, "std_meta") in
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let pkt_loc = State.packet_location in
    let vpkt = VRuntime { loc = pkt_loc; obj_name = "packet_in"; } in
    let st = State.insert pkt_loc (CoreObject (PacketIn pkt)) st in
    let hdr =
      init_val_of_typ env (snd (List.nth_exn params 1)).typ in
    let meta =
      init_val_of_typ env (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init_val_of_typ env (snd (List.nth_exn params 3)).typ in
    let std_meta_type =
      (snd (List.nth_exn params 3)).typ
    in
    let env =
      EvalEnv.(env
              |> insert_val pkt_name      vpkt
              |> insert_val hdr_name      hdr
              |> insert_val meta_name     meta
              |> insert_val std_meta_name std_meta
              |> insert_typ pkt_name      (snd (List.nth_exn params 0)).typ
              |> insert_typ hdr_name      (snd (List.nth_exn params 1)).typ
              |> insert_typ meta_name     (snd (List.nth_exn params 2)).typ
              |> insert_typ std_meta_name std_meta_type)
    in
    (* TODO: implement a more responsible way to generate variable names *)
    let nine = Bigint.((one + one + one) * (one + one + one)) in
    let (env, _) = 
      assign_lvalue 
        env
        ({lval = LMember{expr = {lval = LName {name = std_meta_name}; typ = std_meta_type};
                         name = "ingress_port"};
          typ = Bit {width = 9}})
        (VBit{w = nine; v = in_port}) in
    let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = (Name pkt_name); dir = InOut; typ = (snd (List.nth_exn params 0)).typ}) in
    let hdr_expr =
      Some (Info.dummy, {expr = (Name hdr_name); dir = InOut; typ = (snd (List.nth_exn params 1)).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = (Name meta_name); dir = InOut; typ = (snd (List.nth_exn params 2)).typ}) in
    let std_meta_expr =
      Some (Info.dummy, {expr = (Name std_meta_name); dir = InOut; typ = (snd (List.nth_exn params 3)).typ}) in
    let env = EvalEnv.set_namespace "p." env in
    let (env, st, state,_) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let env = EvalEnv.set_namespace "" env in
    let (env,st) =
      match state with 
      | SReject err -> 
         let err_field =
           { lval = LMember {expr = { lval = LName {name = std_meta_name}; typ = std_meta_type};
                             name = "parser_error"};
             typ = Error}
         in
         assign_lvalue env err_field (VError err)
         |> fst, st
      | SContinue -> (env,st)
      | _ -> failwith "parser should not exit or return" in
    let pktout_loc = State.packet_location in 
    let vpkt' = VRuntime { loc = pktout_loc; obj_name = "packet_out"; } in
    let st = 
      State.insert 
        pktout_loc 
        (CoreObject (PacketOut (Cstruct.create 0, State.find pkt_loc st
                                                  |> assert_pkt))) st in
    let env = EvalEnv.insert_val pkt_name vpkt' env in
    let env = EvalEnv.insert_typ pkt_name (snd (List.nth_exn deparse_params 0)).typ env in
    let (env,st,_) = 
      (env,st)
      |> eval_v1control ctrl app "vr."  verify   [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app "ig."  ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app "eg."  egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app "ck."  compute  [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app "dep." deparser [pkt_expr; hdr_expr] in
    match EvalEnv.find_val pkt_name env with
    | VRuntime {loc; _ } -> 
      begin match State.find loc st with 
        | CoreObject (PacketOut(p0,p1)) -> st, env, Cstruct.append p0 p1
        | _ -> failwith "not a packet" 
      end
    | _ -> failwith "pack not a packet"
