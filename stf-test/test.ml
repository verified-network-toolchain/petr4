open Ast
open Petr4
open Common
open OUnit2

let stmt_string s =
  match s with
  | Expect(port, Some(expect)) ->
    "port: " ^ port ^" expect: " ^ expect
  | Packet(port, packet) ->
    "port: " ^ port ^" packet: " ^ packet
  | _ -> failwith "unimplemented"


let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf: Parse_config =
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
    let in_chan = Unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let _ = Unix.close_process_in in_chan in
    str
end

module Petr4_parse = Make_parse(Conf)

let empty_ctrl =
{|{
  "pre_entries": [],
  "matches": []
  }
|}

let ctrl_json = Yojson.Safe.from_string empty_ctrl

let strip_spaces s = s |> String.split_on_char ' ' |> String.concat ""

let evaler dir name pkt_in =
  Petr4_parse.eval_file ("../examples":: dir) name false pkt_in ctrl_json
  |> strip_spaces

let pp_string s = "\"" ^ s ^ "\""

let run_test dirs name (results, pkt_out) stmt =
    match stmt with
  | Expect(port, Some(expect)) -> begin
    match pkt_out with
    | Some p -> (name >:: fun _ -> assert_equal expect p ~printer:pp_string)::results, pkt_out
    | None -> (name >:: fun _ -> assert_string "no packet")::results, pkt_out
  end
  | Packet(port, packet) ->
    results, Some(evaler dirs name packet)
  | _ -> failwith "unimplemented"

let main include_dir stf_file =
    let f_name =
      (match String.split_on_char '.' stf_file |> List.rev with
      | h::t -> "p4" :: t
      | [] -> failwith "must be stf file") |> List.rev |> String.concat "." in
    let ic = open_in stf_file in
    (* let lexbuf = Lexing.from_string str in *)
    let lexbuf = Lexing.from_channel ic in
    let stmts = Test_parser.statements Test_lexer.token lexbuf in
    List.length stmts |> string_of_int |> print_endline;
    stmts |> List.map stmt_string |> String.concat "\n" |> print_endline;
    let tests = List.fold_left (run_test include_dir f_name) ([], None) stmts |> fst |> List.rev in
    let suite = "suite" ^ stf_file >::: tests in
    run_test_tt_main suite


let command =
  let open Core in
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Foobar"
    (empty
    +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
    +> anon ("stf_file" %: string)
    )
    (fun include_dir stf_file () ->
      print_endline stf_file;
      main include_dir stf_file)

let _ = Core.Command.run command
