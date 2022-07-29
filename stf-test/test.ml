open Petr4.Ast
open Petr4.P4light
open Core

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

let strip_spaces s = s |> String.split_on_chars ~on:([' ']) |> String.concat ~sep:""

let pp_string s = "\"" ^ s ^ "\""

let unimplemented_stmt = function
  | Packet(_, _) | Expect(_, _) -> false
  | _ -> true

let packet_equal (port_exp, pkt_exp) (port, pkt) =
  let (=) = Char.equal in
  let rec iter i =
    i >= String.length pkt_exp ||
    ((pkt_exp.[i] = pkt.[i] || pkt_exp.[i] = '*') && iter (i + 1))
    in
    Int.((port_exp |> Int.of_string) = (port |> Int.of_string)) &&
    iter 0

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
    ((st * Bigint.t) * bool list)
    option
end

module MakeRunner (C : RunnerConfig) = struct  

  let evaler
        (prog : program)
        (pkt_in : string)
        (port : int)
        (st : C.st)
     : ((C.st * Bigint.t) * bool list) option =
    let pkt_in = pkt_in |> String.lowercase |> Cstruct.of_hex |> Cstruct.to_string |> Petr4.Util.string_to_bits in
    let port = Bigint.of_int port in
    C.eval_program prog st port pkt_in

  let update lst name v =
    match List.findi lst ~f:(fun _ (n,_) -> String.(n = name)) with
    | None ->
      (name, [v]) :: lst
    | Some (index, item) ->
      let xs, ys = List.split_n lst index in
      match ys with
      | y :: ys -> xs @ (name, v :: snd item) :: ys
      | [] -> failwith "unreachable: index out of bounds"

  let rec run_test
            (prog : program)
            (stmts : statement list)
            (results : (string * string) list)
            (expected : (string * string) list)
            (st : C.st)
      : ((string * string) list) * ((string * string) list) = 
    match stmts with
    | [] -> (expected, results)
    | hd :: tl -> 
      match hd with
      | Packet (port, packet) -> 
         let results', st' =
           match evaler prog packet (int_of_string port) st with
           | Some ((st', port), pkt) ->
              let fixed = pkt |> Petr4.Util.bits_to_string |> Petr4.Util.hex_of_string |> strip_spaces |> String.lowercase in
              (Bigint.to_string port, fixed) :: results, st'
           | None ->
              results, st
         in
         run_test prog tl results' expected st'
      | Expect (port, Some packet) ->
         run_test prog tl results ((port, strip_spaces packet |> String.lowercase) :: expected) st
         (*
      | Add (tbl_name, priority, match_list, (action_name, args), id) ->
        let tbl_name = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let entry = Poulet4.Target.Coq_mk_table_entry (match_list, action_name') in
        let st' = Poulet4.Semantics.add_entry _ st tbl_name entry in
        run_test prog tl results expected st'
          *)
      | Wait ->
         Core_unix.sleep 1;
         run_test prog tl results expected st
  (*
      | Set_default (tbl_name, (action_name, args)) ->
        let tbl_name' = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let set_def' = update set_def tbl_name' (action_name', args) in
        run_test prog tl results expected env st
   *)
      | _ -> failwith "unimplemented stf statement"
end

module V1RunnerConfig = struct
  type st = Obj.t Poulet4.Maps.PathMap.t
  let eval_program = Petr4.Eval.v1_interp
end

module V1Runner = MakeRunner(V1RunnerConfig)

let get_stf_files path =
  Sys_unix.ls_dir path |> Base.List.to_list |>
  List.filter ~f:(fun x -> Core.Filename.check_suffix x ".stf")

let run_stf stf_file p4prog =
    let ic = In_channel.create stf_file in
    let lexbuf = Lexing.from_channel ic in
    let stmts = Test_parser.statements Test_lexer.token lexbuf in
    let _, prog = 
      p4prog
      |> Petr4.Elaborate.elab
      |> fun (prog, renamer) ->
         Petr4.Checker.check_program renamer prog
    in
    let target =
      prog
      |> List.rev
      |> List.hd_exn 
      |> function | Poulet4.Syntax.DeclInstantiation (_, typ, _, _, _) -> typ
                  | _ -> failwith "unexpected main value"
    in
    match target with
    | TypSpecializedType (TypTypeName {str = "V1Switch"; _}, _) -> 
      V1Runner.run_test prog stmts [] [] (fun _ -> None)
    | _ -> failwith "architecture unsupported"

let stf_alco_test stf_file p4_file p4prog =
    let run_stf_alcotest () =
      let expected, results = run_stf stf_file p4prog in
      List.zip_exn expected results |> List.iter ~f:(fun (p_exp, p) ->
            Alcotest.(testable (Fmt.pair ~sep:Fmt.sp Fmt.string Fmt.string) packet_equal |> check) "packet test" p_exp p)
    in
    let test = Alcotest.test_case (Filename.basename p4_file) `Quick run_stf_alcotest in
    test
