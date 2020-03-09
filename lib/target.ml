module I = Info
open Value
open Env
open Types
open Core
module Info = I

type extern = EvalEnv.t -> value list -> EvalEnv.t * value

(* module type State = sig
  type loc = int
  type 'a t
  val empty : 'a t
  val insert : loc -> 'a -> 'a t -> 'a t
  val find : loc -> 'a t -> 'a
  val fresh_loc : unit -> loc
end *)

module State = struct 
  type loc = int
  type 'a t = (loc * 'a) list

  let empty = []

  let insert loc v st = (loc, v) :: st
  
  let find loc st = List.Assoc.find_exn (* TODO *) st loc ~equal:Int.equal

  let fresh_loc = 
    let counter = ref 0 in
    (fun () -> counter := !counter + 1; !counter)

end

module type Target = sig

  type obj
  type st

  val empty_state : st
  val insert : int -> obj -> st -> st
  val find : int -> st -> obj
  val fresh_loc : unit -> int

  val obj_mem : obj -> string -> value

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  (ctrl -> EvalEnv.t -> st -> lvalue -> value -> EvalEnv.t * st * 'b) -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

module Core = struct

  type obj = 
    | PacketIn of Cstruct_sexp.t
    | PacketOut of Cstruct_sexp.t * Cstruct_sexp.t

  let pktin_mem mname = 
    match mname with 
    | _ -> failwith "TODO"

  let pktout_mem mname = 
    match mname with 
    | _ -> failwith "TODO"

  let obj_mem obj mname =
    match obj with
    | PacketIn _ -> pktin_mem mname
    | PacketOut _ -> pktout_mem mname

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

  type obj = 
    | CoreObject of Core.obj
    (* | V1Object of unit *) (* TODO *)

  type st = obj State.t

  let empty_state = State.empty

  let insert = State.insert
  let find = State.find
  let fresh_loc = State.fresh_loc

  let obj_mem (obj : obj) (mname : string) : value = 
    match obj with 
    | CoreObject cobj -> Core.obj_mem cobj mname

  let assert_pkt = function
    | CoreObject (PacketIn pkt) -> pkt
    | _ -> failwith "TODO"

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
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let pkt_loc = State.fresh_loc () in
    let vpkt = VRuntime pkt_loc in
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
    let vpkt' = VRuntime pktout_loc in
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
    | VRuntime loc -> 
      begin match State.find loc st with 
        | CoreObject (PacketOut(p0,p1)) -> st, Cstruct.append p0 p1
        | _ -> failwith "not a packet" end
    | _ -> failwith "pack not a packet"

end

module EbpfFilter  = struct 

  type st = unit

  let empty_state = ()

  let externs = []

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
