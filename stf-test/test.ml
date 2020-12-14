open Petr4
open Petr4.Ast
open Common
open Core

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

  val eval_program : Prog.Value.ctrl -> Prog.Env.EvalEnv.t -> st -> Prog.Value.buf ->
    Bigint.t -> Prog.program -> st * (Prog.Value.buf * Bigint.t) option
end

module MakeRunner (C : RunnerConfig) = struct  

  let evaler (prog : Prog.program) (pkt_in : string) (port : int)
      (env : Prog.Env.EvalEnv.t) (st : C.st) add : C.st * (Prog.Value.buf * Bigint.t) option =
    let pkt_in = Cstruct.of_hex pkt_in in
    let port = Bigint.of_int port in
    C.eval_program (add, []) env st pkt_in port prog

  let update lst name v =
    match List.findi lst ~f:(fun _ (n,_) -> String.(n = name)) with
    | None ->
      (name, [v]) :: lst
    | Some (index, item) ->
      let xs, ys = List.split_n lst index in
      match ys with
      | y :: ys -> xs @ (name, v :: snd item) :: ys
      | [] -> failwith "unreachable: index out of bounds"

  let rec run_test (prog : Prog.program) (stmts : statement list) (add, set_def)
      (results : (string * string) list) (expected : (string * string) list)
      (env : Prog.Env.EvalEnv.t) (st : C.st)
      : ((string * string) list) * ((string * string) list) = 
    match stmts with
    | [] -> (expected, results)
    | hd :: tl -> 
      match hd with
      | Packet (port, packet) -> 
        let (st', result) = evaler prog (packet |> String.lowercase) (int_of_string port) env st (add,set_def) in
        let results' =
        begin match result with
        | Some (pkt, port) ->
                let fixed = pkt |> Cstruct.to_string |> Petr4_parse.hex_of_string |> strip_spaces |> String.lowercase in
                (Bigint.to_string port, fixed) :: results
        | None -> results
        end in
        run_test prog tl (add,set_def) results' expected env st'
      | Expect (port, Some packet) -> run_test prog tl (add,set_def) results ((port, strip_spaces packet |> String.lowercase) :: expected) env st
      | Add (tbl_name, priority, match_list, (action_name, args), id) ->
        let tbl_name' = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let add' = update add tbl_name' (priority, match_list, (action_name', args), id) in 
        run_test prog tl (add',set_def) results expected env st
      | Wait -> Unix.sleep 1; run_test prog tl (add,set_def) results expected env st
      | Set_default (tbl_name, (action_name, args)) ->
        let tbl_name' = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let set_def' = update set_def tbl_name' (action_name', args) in
        run_test prog tl (add, set_def') results expected env st
      | _ -> failwith "unimplemented stf statement"
end

module MakeConfig (I : Eval.Interpreter) = struct
  type st = I.state

  let eval_program = I.eval_program
end

module V1RunnerConfig = MakeConfig(Eval.V1Interpreter)

module V1Runner = MakeRunner(V1RunnerConfig)

module EbpfRunnerConfig = MakeConfig(Eval.EbpfInterpreter)

module EbpfRunner = MakeRunner(EbpfRunnerConfig)

module Up4RunnerConfig = MakeConfig(Eval.Up4Interpreter)

module Up4Runner = MakeRunner(Up4RunnerConfig)

let get_stf_files path =
  Sys.ls_dir path |> Base.List.to_list |>
  List.filter ~f:(fun x -> Core.Filename.check_suffix x ".stf")

let run_stf include_dir stf_file p4_file =
    let ic = In_channel.create stf_file in
    let lexbuf = Lexing.from_channel ic in
    let stmts = Test_parser.statements Test_lexer.token lexbuf in
    let env, prog = 
      Petr4_parse.parse_file include_dir p4_file false
      |> (function `Ok p -> p | _ -> failwith "Petr4 parser error")
      |> Elaborate.elab
      |> fun (prog, renamer) -> Checker.check_program renamer prog
      |> Tuple.T2.map_fst ~f:Env.CheckerEnv.eval_env_of_t in
    let target = match prog with Program l ->
      l
      |> List.rev |> List.hd_exn |> snd
      |> function Prog.Declaration.Instantiation{typ;_} -> typ
         | _ -> failwith "unexpected main value" in
    match target with
    | SpecializedType{base = TypeName (BareName(_, "V1Switch"));_} -> 
      V1Runner.run_test prog stmts ([],[]) [] [] env Eval.V1Interpreter.empty_state
    | SpecializedType{base = TypeName (BareName(_, "ebpfFilter"));_} ->
      EbpfRunner.run_test prog stmts ([],[]) [] [] env Eval.EbpfInterpreter.empty_state
    | SpecializedType{base = TypeName (BareName(_, "uP4Switch"));_} ->
      Up4Runner.run_test prog stmts ([],[]) [] [] env Eval.Up4Interpreter.empty_state
    | _ -> failwith "architecture unsupported"

let stf_alco_test include_dir stf_file p4_file =
    let run_stf_alcotest () =
      let expected, results = run_stf include_dir stf_file p4_file in
      List.zip_exn expected results |> List.iter ~f:(fun (p_exp, p) ->
            Alcotest.(testable (Fmt.pair ~sep:Fmt.sp Fmt.string Fmt.string) packet_equal |> check) "packet test" p_exp p)
    in
    let test = Alcotest.test_case p4_file `Quick run_stf_alcotest in
    test
