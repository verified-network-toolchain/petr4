module I = Info
open Value
open Env
open Types
open Core
module Info = I

type extern = EvalEnv.t -> value list -> EvalEnv.t * value

module type Target = sig

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit

  val eval_pipeline : EvalEnv.t -> ctrl -> packet_in -> 
  (EvalEnv.t -> ctrl -> signal -> value -> Argument.t list -> EvalEnv.t * signal * 'a) -> 
  (EvalEnv.t -> ctrl -> lvalue -> value -> EvalEnv.t * 'b) -> 
  (EvalEnv.t -> ctrl -> string -> Type.t -> value) -> packet_in

end

module Core : Target = struct 

  let eval_extract_fixed env pkt v =
    failwith "unimplemented"
  
  let eval_extract_var env pkt v1 v2 =
    failwith "unimplemented"

  let eval_extract env args = 
    match args with 
    | [pkt;v1] -> eval_extract_fixed env pkt v1 
    | [pkt;v1;v2] -> eval_extract_var env pkt v1 v2 
    | _ -> failwith "wrong number of args for extract"

  let eval_lookahead env args =
    failwith "unimplemented"

  let eval_advance env args = 
    failwith "unimplemented"

  let eval_length env args = 
    failwith "unimplemented"

  let eval_emit env args =
    failwith "unimplemented"

  let eval_verify env args =
    failwith "unimplemented"

  let externs = [("extract", eval_extract);
                 ("lookahead", eval_lookahead);
                 ("advance", eval_advance);
                 ("length", eval_length);
                 ("emit", eval_emit);
                 ("verify", eval_verify)]

  let check_pipeline = failwith "core has no pipeline"

  let eval_pipeline = failwith "core has no pipeline"

end 

module V1Model : Target = struct

  let externs = []

  let check_pipeline env = ()

  let eval_v1control (ctrl : ctrl) (app) (control : value)
      (args : Argument.t list) (env : EvalEnv.t) : EvalEnv.t * signal =
    let (env,s,_) = app env ctrl SContinue control args in
    (env,s)

  let eval_pipeline env ctrl pkt app assign init =
    let main = EvalEnv.find_val "main" env in
    let vs = assert_package main |> snd in
    let parser =
      List.Assoc.find_exn vs "p"   ~equal:(=) in
    let verify =
      List.Assoc.find_exn vs "vr"  ~equal:(=) in
    let ingress =
      List.Assoc.find_exn vs "ig"  ~equal:(=) in
    let egress =
      List.Assoc.find_exn vs "eg"  ~equal:(=) in
    let compute =
      List.Assoc.find_exn vs "ck"  ~equal:(=) in
    let deparser =
      List.Assoc.find_exn vs "dep" ~equal:(=) in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let vpkt = VRuntime (PacketIn pkt) in
    let hdr =
      init env ctrl "hdr"      (snd (List.nth_exn params 1)).typ in
    let meta =
      init env ctrl "meta"     (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init env ctrl "std_meta" (snd (List.nth_exn params 3)).typ in
    let env =
      EvalEnv.(env
              |> insert_val "packet"   vpkt
              |> insert_val "hdr"      hdr
              |> insert_val "meta"     meta
              |> insert_val "std_meta" std_meta
              |> insert_typ "packet"   (snd (List.nth_exn params 0)).typ
              |> insert_typ "hdr"      (snd (List.nth_exn params 1)).typ
              |> insert_typ "meta"     (snd (List.nth_exn params 2)).typ
              |> insert_typ "std_meta" (snd (List.nth_exn params 3)).typ) in
    (* TODO: implement a more responsible way to generate variable names *)
    let pkt_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
    let hdr_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
    let meta_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "meta"))}) in
    let std_meta_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "std_meta"))}) in
    let (env, state, _) =
      app env ctrl SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let env = 
      match state with 
      | SReject err -> 
        assign env ctrl (LMember{expr=LName("std_meta");name="parser_error"}) (VError(err)) 
        |> fst
      | SContinue -> env 
      | _ -> failwith "parser should not exit or return" in
    let vpkt' =
      VRuntime (PacketOut(Cstruct.create 0, EvalEnv.find_val "packet" env
                                            |> assert_runtime
                                            |> assert_packet_in)) in
    let env = EvalEnv.insert_val "packet" vpkt' env in
    let (env, _) = env
              |> eval_v1control ctrl app verify   [hdr_expr; meta_expr] |> fst
              |> eval_v1control ctrl app ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst
              |> eval_v1control ctrl app egress   [hdr_expr; meta_expr; std_meta_expr] |> fst
              |> eval_v1control ctrl app compute  [hdr_expr; meta_expr] |> fst
              |> eval_v1control ctrl app deparser [pkt_expr; hdr_expr] in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> Cstruct.append p0 p1
    | _ -> failwith "pack not a packet"

end

module EbpfFilter : Target = struct 

  let externs = []

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Argument.t list) app
  (env : EvalEnv.t) : EvalEnv.t * signal =
    let (env,s,_) = app env ctrl SContinue control args in 
    (env,s)

  let eval_pipeline env ctrl pkt app assign init = 
    let main = EvalEnv.find_val "main" env in
    let vs = assert_package main |> snd in
    let parser = List.Assoc.find_exn vs "prs"  ~equal:(=) in 
    let filter = List.Assoc.find_exn vs "filt" ~equal:(=) in
    let params = 
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let pckt = VRuntime (PacketIn pkt) in
    let hdr = init env ctrl "hdr" (snd (List.nth_exn params 1)).typ in
    let accept = VBool (false) in
    let env =
      EvalEnv.(env 
               |> insert_val "packet" pckt 
               |> insert_val "hdr"    hdr
               |> insert_val "accept" accept
               |> insert_typ "packet" (snd (List.nth_exn params 0)).typ
               |> insert_typ "hdr"    (snd (List.nth_exn params 1)).typ 
               |> insert_typ "accept" (Info.dummy, Type.Bool)) in
    let pckt_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
    let hdr_expr = 
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
    let accept_expr =
      (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "accept"))}) in
    let (env, state, _) =
      app env ctrl SContinue parser [pckt_expr; hdr_expr] in
    let env = 
      match state with 
      | SReject _ -> assign env ctrl (LName("accept")) (VBool(false)) |> fst
      | SContinue ->  env |> eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app |> fst 
      | _ -> failwith "parser should not exit or return" in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> Cstruct.append p0 p1
    | _ -> failwith "pack not a packet"

end
