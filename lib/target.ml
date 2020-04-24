module I = Info
open Value
open Env
open Types
open Core
module Info = I

type 'st assign =
  ctrl -> EvalEnv.t -> 'st -> lvalue -> value -> EvalEnv.t * 'st * signal

type ('st1, 'st2) pre_extern =
  'st1 assign -> ctrl -> EvalEnv.t -> 'st2 -> value list ->
  EvalEnv.t * 'st2 * signal * value

module State = struct

  type 'a t = (int * 'a) list

  let empty = []

  let insert loc v st = (loc, v) :: st
  
  let find loc st = List.Assoc.find_exn (* TODO *) st loc ~equal:Int.equal

  let fresh_loc = 
    let counter = ref 0 in
    (fun () -> counter := !counter + 1; !counter)

end

module type Target = sig

  type obj

  type st = obj State.t

  type 'st extern = ('st, st) pre_extern

  val externs : (string * st extern) list

  val eval_extern : 'st assign -> ctrl -> EvalEnv.t -> st -> value list ->
                    string -> EvalEnv.t * st * signal * value

  val check_pipeline : EvalEnv.t -> unit

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  st assign -> (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

module Core = struct

  type obj = 
    | PacketIn of pkt
    | PacketOut of pkt_out

  type st = obj State.t

  type 'st extern = ('st, st) pre_extern

  let eval_extract_fixed assign ctrl env st pkt v =
    failwith "unimplemented"
  
  let eval_extract_var env st pkt v1 v2 =
    failwith "unimplemented"

  let eval_extract : 'st extern = fun assign ctrl env st args ->
    match args with 
    | [pkt;v1] -> eval_extract_fixed assign ctrl env st pkt v1 
    | [pkt;v1;v2] -> eval_extract_var env st pkt v1 v2 
    | _ -> failwith "wrong number of args for extract"

  let eval_lookahead : 'st extern = fun env st args ->
    failwith "unimplemented"

  let eval_advance : 'st extern = fun env st args ->
    failwith "unimplemented"

  let eval_length : 'st extern = fun _ _ env st args ->
    match args with
    | [VRuntime {loc;_}] ->
      let obj = State.find loc st in
      let len = 
        match obj with
        | PacketIn pkt -> Cstruct.len pkt
        | PacketOut _ -> failwith "expected packet_in" in
      env, st, SContinue, VBit {w= Bigint.of_int 3; v = Bigint.of_int len }
    | _ -> failwith "unexpected args for length"

  let eval_emit : 'st extern = fun env st args ->
    failwith "unimplemented"

  let eval_verify : 'st extern = fun _ _ env st args ->
    let b, err = match args with
      | [VBool b; VError err] -> b, err
      | _ -> failwith "unexpected args for verify" in
    if b then env, st, SContinue, VNull
    else env, st, SReject err, VNull

  let externs : (string * 'st extern) list =
    [ ("extract", eval_extract);
      ("lookahead", eval_lookahead);
      ("advance", eval_advance);
      ("length", eval_length);
      ("emit", eval_emit);
      ("verify", eval_verify)]

  let eval_extern assign ctrl env st vs name =
    let extern = List.Assoc.find_exn name externs in
    extern assign ctrl env st vs

  let check_pipeline _ = ()

  let eval_pipeline _ _ st pkt _ _ _ = st, pkt

end 

module V1Model : Target = struct

  type obj =
    | CoreObject of Core.obj
    (* | V1Object of v1object *)

  (* and v1object = unit *)
    (* | Counter of unit TODO *)

  type st = obj State.t

  type 'st extern = ('st, st) pre_extern

  let assert_pkt = function
    | CoreObject (PacketIn pkt) -> pkt
    | CoreObject _ -> failwith "not a packet"

  let assert_core = function
    | CoreObject o -> o
    (* | _ -> failwith "expected core object" *)

  let is_core = function
    | CoreObject _ -> true
    (* | _ -> false *)

  let v1externs = [ (* TODO *) ]

  let corize_st (st : st) : Core.st =
    st
    |> List.filter ~f:(fun (_, o) -> is_core o)
    |> List.map ~f:(fun (i, o) -> (i, assert_core o))

  let targetize_st (st : Core.st) : st = 
    st
    |> List.map ~f:(fun (i, o) -> i, CoreObject o)

  let targetize (ext : 'st Core.extern) : 'st extern =
    fun assign ctrl env st vs ->
    let (env', st', s, v) = ext assign ctrl env (corize_st st) vs in
    env', targetize_st st' @ st, s, v

  let externs =
    v1externs @ (List.map Core.externs ~f:(fun (n, e) -> n, targetize e))

  let eval_extern _ = failwith ""

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
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let pkt_loc = State.fresh_loc () in
    let vpkt = VRuntime { loc = pkt_loc; typ_name = "packet_in"; } in
    let st = State.insert pkt_loc (CoreObject (PacketIn pkt)) st in
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
    let pktout_loc = State.fresh_loc () in 
    let vpkt' = VRuntime { loc = pktout_loc; typ_name = "packet_out"; } in
    let st = 
      State.insert 
        pktout_loc 
        (CoreObject (PacketOut (Cstruct.create 0, State.find pkt_loc st
                                                  |> assert_pkt))) st in
    let env = EvalEnv.insert_val "packet" vpkt' env in
    let env = EvalEnv.insert_typ "packet" (snd (List.nth_exn deparse_params 0)).typ env in (* TODO: add type to env here *)
    let (env,st,_) = 
      (env,st)
      |> eval_v1control ctrl app verify   [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app egress   [hdr_expr; meta_expr; std_meta_expr] |> fst23
      |> eval_v1control ctrl app compute  [hdr_expr; meta_expr] |> fst23
      |> eval_v1control ctrl app deparser [pkt_expr; hdr_expr] in
    print_endline "After runtime evaluation";
    EvalEnv.print_env env;
    match EvalEnv.find_val "packet" env with
    | VRuntime {loc; _ } -> 
      begin match State.find loc st with 
        | CoreObject (PacketOut(p0,p1)) -> st, Cstruct.append p0 p1
        | _ -> failwith "not a packet" 
      end
    | _ -> failwith "pack not a packet"

end

module EbpfFilter : Target = struct 

  type obj = unit (* TODO *)

  type st = obj State.t

  type 'st extern = ('st, st) pre_extern

  let externs = []

  let eval_extern _ = failwith ""

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Argument.t list) app
  (env,st) : EvalEnv.t * st * signal =
    let (env,st,s,_) = app ctrl env st SContinue control args in 
    (env,st,s)

  let eval_pipeline ctrl env st pkt app assign init = failwith "TODO"
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
    | VRuntime (PacketOut(p0,p1)) -> ( (), Cstruct.append p0 p1) *)
    (* | _ -> failwith "pack not a packet" *)

end
