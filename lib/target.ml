module I = Info
open Value
open Env
open Types
open Core_kernel
module Info = I

type extern = EvalEnv.t -> value list -> EvalEnv.t * value

module type Target = sig

  type st

  val dummy_st : st

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  (ctrl -> EvalEnv.t -> st -> lvalue -> value -> EvalEnv.t * st * 'b) -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

module Core : Target = struct

  type st = unit

  let dummy_st = ()

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

  let check_pipeline _ = failwith "core has no pipeline"

  let eval_pipeline _ = failwith "core has no pipeline"

end

module V1Model : Target = struct

  type st = unit

  let dummy_st = ()

  let externs = []

  let check_pipeline env = ()

  let eval_v1control (ctrl : ctrl) (app) (control : value)
      (args : Argument.t list) (env,st) : EvalEnv.t * st * signal =
    let (env,st',s,_) = app ctrl env st SContinue control args in
    (env,st',s)

  let eval_pipeline ctrl env st pkt app assign init =
    let fst23 (a,b,_) = (a,b) in  
    let main = EvalEnv.find_val "main" env in
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
    let vpkt = VRuntime (PacketIn pkt) in
    let hdr =
      init ctrl env st "hdr"      (snd (List.nth_exn params 1)).typ in
    let meta =
      init ctrl env st "meta"     (snd (List.nth_exn params 2)).typ in
    let std_meta =
      init ctrl env st "std_meta" (snd (List.nth_exn params 3)).typ in
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
    let (env, st, state,_) =
      app ctrl env st SContinue parser [pkt_expr; hdr_expr; meta_expr; std_meta_expr] in
    let (env,st) = 
      match state with 
      | SReject err -> 
        assign ctrl env st (LMember{expr=LName("std_meta");name="parser_error"}) (VError(err)) 
        |> fst23
      | SContinue -> (env,st)
      | _ -> failwith "parser should not exit or return" in
    let vpkt' =
      VRuntime (PacketOut(Cstruct.create 0, EvalEnv.find_val "packet" env
                                            |> assert_runtime
                                            |> assert_pkt)) in
    let env = EvalEnv.insert_val "packet" vpkt' env in
    let (env,st,_) = (env,st)
              |> eval_v1control ctrl app verify   [hdr_expr; meta_expr] |> fst23
              |> eval_v1control ctrl app ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
              |> eval_v1control ctrl app egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
              |> eval_v1control ctrl app compute  [hdr_expr; meta_expr] |> fst23
              |> eval_v1control ctrl app deparser [pkt_expr; hdr_expr] in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1)
    | _ -> failwith "pack not a packet"

end

module EbpfFilter : Target = struct

  type st = unit

  let dummy_st = ()

  let externs = []

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Argument.t list) app
  (env,st) : EvalEnv.t * st * signal =
    let (env,st,s,_) = app ctrl env st SContinue control args in 
    (env,st,s)

  let eval_pipeline ctrl env st pkt app assign init = 
    let main = EvalEnv.find_val "main" env in
    let vs = assert_package main |> snd in
    let parser = List.Assoc.find_exn vs "prs"  ~equal:String.equal in
    let filter = List.Assoc.find_exn vs "filt" ~equal:String.equal in
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let pckt = VRuntime (PacketIn pkt) in
    let hdr = init ctrl env st "hdr" (snd (List.nth_exn params 1)).typ in
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
    let (env, st,state, _) =
      app ctrl env st SContinue parser [pckt_expr; hdr_expr] in
    let fst23 (a,b,_) = (a,b) in
    let (env,st) = 
      match state with 
      | SReject _ -> assign ctrl env st (LName("accept")) (VBool(false)) |> fst23
      | SContinue ->  (env,st) |> eval_ebpf_ctrl ctrl filter [hdr_expr; accept_expr] app |> fst23 
      | _ -> failwith "parser should not exit or return" in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1)
    | _ -> failwith "pack not a packet"

end
