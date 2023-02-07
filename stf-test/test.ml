open Petr4.Ast
open Petr4.P4light
open Core
module R = Poulet4.Result
module Exn = Poulet4.Target.Exn

let stmt_string s =
  match s with
  | Expect(port, Some(expect)) ->
    "port: " ^ port ^" expect: " ^ expect
  | Packet(port, packet) ->
    "port: " ^ port ^" packet: " ^ packet
  | _ -> failwith "unimplemented"


let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf =
struct
  open Core
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s

  let preprocess include_dirs p4file =
    let cmd =
      String.concat ~sep:" "
        (["cc"] @
        (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
          ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
    let in_chan = Core_unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let _ = Core_unix.close_process_in in_chan in
    str
end

let empty_ctrl =
{|{
  "pre_entries": [],
  "matches": []
  }
|}

let ctrl_json = Yojson.Safe.from_string empty_ctrl

let pp_string s = "\"" ^ s ^ "\""

let unimplemented_stmt = function
  | Packet(_, _) | Expect(_, _) -> false
  | _ -> true

let packet_equal (port_exp, pkt_exp) (port, pkt) =
  let matches_exp idx char =
    if idx >= String.length pkt_exp
    then false
    else let char_exp = pkt_exp.[idx] in
      Char.equal char_exp char || Char.equal char_exp '*'
  in
  Int.equal (Int.of_string port_exp) (Int.of_string port) &&
  String.for_alli ~f:matches_exp pkt

let convert_qualified name =
  match String.rindex name '.' with 
  | None -> name
  | Some idx -> 
    let length = String.length name in
    String.slice name (idx + 1) length

module type RunnerConfig = sig
  type st

  val eval_program :
    program ->
    st -> 
    Bigint.t ->
    bool list ->
    (Exn.t, (st * Bigint.t) * bool list) R.result
end

module MakeRunner (C : RunnerConfig) = struct  

  let update lst name v =
    match List.findi lst ~f:(fun _ (n,_) -> String.(n = name)) with
    | None ->
      (name, [v]) :: lst
    | Some (index, item) ->
      let xs, ys = List.split_n lst index in
      match ys with
      | y :: ys -> xs @ (name, v :: snd item) :: ys
      | [] -> failwith "unreachable: index out of bounds"
end

module V1RunnerConfig = struct
  type st = Obj.t Poulet4.Maps.PathMap.t
  let eval_program = Petr4.Eval.v1_interp
end

module V1Runner = MakeRunner(V1RunnerConfig)

let get_stf_files path =
  Sys_unix.ls_dir path |> Base.List.to_list |>
  List.filter ~f:(fun x -> Core.Filename.check_suffix x ".stf")

let stf_alco_test include_dir stf_file p4_file =
    let run_stf_alcotest () =
      let cfg = Petr4.Pass.mk_check_only include_dir p4_file in
      let p4_prog = Petr4.Unix.Driver.run_checker cfg
                    |> Petr4.Common.handle_error in
      let expected, results = Petr4.Stf.run_stf stf_file p4_prog in
      List.zip_exn expected results
      |> List.iter ~f:(fun (p_exp, p) ->
          Alcotest.(testable (Fmt.pair ~sep:Fmt.sp Fmt.string Fmt.string) packet_equal |> check) "packet test" p_exp p)
    in
    let test = Alcotest.test_case (Filename.basename p4_file) `Quick run_stf_alcotest in
    test
