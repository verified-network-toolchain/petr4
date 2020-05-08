open Typed
open Prog
open Value
open Env
open Target
module I = Info
open Core_kernel
module Info = I

type obj =
  | CoreObject of P4core.obj
  | V1Object of v1object

and v1object =
  | Counter of {
      states : Bigint.t list;
      typ : counter_type;
      size : Bigint.t;
    }
  | Register of {
      states: Value.value list;
      size: Bigint.t;
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

let eval_read : extern = fun _ env st _ args ->
  match args with
  | [(VRuntime {loc;_}, _); _ ; (VBit {w = w; v = v}, _)] ->
    let reg_obj = State.find loc st in
    let states = match reg_obj with
                  | V1Object x -> ( match x with
                      | Register {states; _} -> states
                      | _ -> failwith "Reading from an object other than a v1 register")
                  | _ -> failwith "Reading from an object other than a v1 register" in
    let read_val = List.nth_exn states (Bigint.to_int_exn v) in
    let env'= EvalEnv.insert_val (Types.BareName (Info.dummy, "result")) read_val env in 
    env', st, SContinue, read_val
  | _ -> failwith "unexpected args for register read"
  
let eval_register : extern = fun _ env st typs args ->
  let width = match typs with
              | [Typed.Type.Bit w] -> w.width
              | _ -> 32 in
  match args with
  | [(VRuntime {loc;obj_name}, _); (VBit {w = _; v = size}, _)] ->
    let init_val = VBit {w = Bigint.of_int width; v = Bigint.zero} in
    let states = List.init (Bigint.to_int_exn size) ~f:(fun _ -> init_val) in 
    let reg = Register {states = states;
                        size = size; } in
    let v = V1Object reg in
    let st' = State.insert loc v st in
    env, st', SContinue, VRuntime {loc = loc; obj_name = obj_name}
  | _ -> failwith "unexpected args for register instantiation"

let eval_write : extern = fun _ env st _ args -> 
  match args with
  | [(VRuntime {loc;_}, _); 
      (VBit {w = _; v = v_index}, _) ; 
      (write_val, _)] ->
    let reg_obj = State.find loc st in
    let states, size = match reg_obj with
                    | V1Object x -> ( match x with
                        | Register {states; size} -> states, size
                        | _ -> failwith "Reading from an object other than a v1 register")
                    | _ -> failwith "Reading from an object other than a v1 register" in
    let subs_f = fun i x -> if i = (Bigint.to_int_exn v_index) then write_val else x in 
    let states' = List.mapi ~f:subs_f states in
    let reg' = Register {states = states';
                          size = size;} in
    let reg_obj' = V1Object reg' in
    let st' = State.insert loc reg_obj' st in
    env, st', SContinue, write_val 
  | _ -> failwith "unexpected args for register write"

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

let corize_st (st : state) : P4core.state =
  st
  |> List.filter ~f:(fun (_, o) -> is_core o)
  |> List.map ~f:(fun (i, o) -> (i, assert_core o))

let targetize_st (st : P4core.state) : state = 
  st
  |> List.map ~f:(fun (i, o) -> i, CoreObject o)

let targetize (ext : P4core.extern) : extern =
  fun ctrl env st ts vs ->
  let (env', st', s, v) =
    ext ctrl env (corize_st st) ts vs in
  env', targetize_st st' @ st, s, v

let externs : (string * extern) list =
  v1externs @ (List.map P4core.externs ~f:(fun (n, e : string * P4core.extern) -> n, targetize e))

let eval_extern name ctrl env st targs args =
  let extern =
    match name with
    | "extract" -> targetize P4core.eval_extract
    | "lookahead" -> targetize P4core.eval_lookahead
    | "advance" -> targetize P4core.eval_advance
    | "length" -> targetize P4core.eval_length
    | "emit" -> targetize P4core.eval_emit
    | "verify" -> targetize P4core.eval_verify
    | "register" -> eval_register
    | "read" -> eval_read
    | "write" -> eval_write
    | _ -> failwith "TODO" in
  extern ctrl env st targs args

let initialize_metadata meta env =
  let nine = Bigint.of_int 9 in
  EvalEnv.insert_val (BareName (Info.dummy, "ingress_port")) (VBit{w=nine; v=meta}) env

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
  let pktout_loc = State.packet_location in 
  let vpkt' = VRuntime { loc = pktout_loc; obj_name = "packet_out"; } in
  let st = 
    State.insert 
      pktout_loc 
      (CoreObject (PacketOut (Cstruct.create 0, State.find pkt_loc st
                                                |> assert_pkt))) st in
  let env = EvalEnv.insert_val (BareName (Info.dummy, "packet")) vpkt' env in
  let env = EvalEnv.insert_typ (BareName (Info.dummy, "packet")) (snd (List.nth_exn deparse_params 0)).typ env in
  let (env,st,_) = 
    (env,st)
    |> eval_v1control ctrl app "vr."  verify   [hdr_expr; meta_expr] |> fst23
    |> eval_v1control ctrl app "ig."  ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
    |> eval_v1control ctrl app "eg."  egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
    |> eval_v1control ctrl app "ck."  compute  [hdr_expr; meta_expr] |> fst23
    |> eval_v1control ctrl app "dep." deparser [pkt_expr; hdr_expr] in
  match EvalEnv.find_val (BareName (Info.dummy, "packet")) env with
  | VRuntime {loc; _ } -> 
    begin match State.find loc st with 
      | CoreObject (PacketOut(p0,p1)) -> st, env, Cstruct.append p0 p1
      | _ -> failwith "not a packet" 
    end
  | _ -> failwith "pack not a packet"