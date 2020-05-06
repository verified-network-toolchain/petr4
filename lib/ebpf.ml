module I = Info
open Target
open Prog
open Value
open Core_kernel
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

type obj = unit (* TODO *)

type state = obj State.t

type extern = state pre_extern

let externs = []

let eval_extern _ = failwith ""

let initialize_metadata meta env =
  env (* TODO *)

let check_pipeline env = failwith "unimplemented"

let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
(env,st) : env * state * signal =
  let (env,st,s,_) = app ctrl env st SContinue control args in 
  (env,st,s)

let eval_pipeline ctrl env st pkt app = failwith "TODO"
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
  let hdr = init_val_of_typ env (snd (List.nth_exn params 1)).typ in
  let accept = VBool (false) in
  let accept_name = BareName (Info.dummy, "accept") in
  let env =
    EvalEnv.(env
             |> insert_val pkt_name    pckt
             |> insert_val hdr_name    hdr
             |> insert_val accept_name accept
             |> insert_typ pkt_name    (snd (List.nth_exn params 0)).typ
             |> insert_typ hdr_name    (snd (List.nth_exn params 1)).typ
             |> insert_typ accept_name (Info.dummy, Type.Bool)) in
  let pckt_expr =
    Info.dummy, Argument.Expression {value = Info.dummy, Name pkt_name} in
  let hdr_expr =
    Info.dummy, Argument.Expression {value = Info.dummy, Name hdr_name} in
  let accept_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "accept"))}) in
  let (env, st,state, _) =
    app ctrl env st SContinue parser [pckt_expr; hdr_expr] in
  let fst23 (a,b,_) = (a,b) in
  let (env,st) = 
    match state with 
    | SReject _ -> assign_lvalue ctrl env st (LName("accept")) (VBool(false)) |> fst23
    | SContinue ->  (env,st) |> eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app |> fst23 
    | _ -> failwith "parser should not exit or return" in
  match EvalEnv.find_val "packet" env with
  | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1) *)
  (* | _ -> failwith "pack not a packet" *)
