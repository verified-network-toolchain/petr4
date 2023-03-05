open Core

type arch =
  | V1Model
  | Tofino

type fmt =
  | Concrete (* valid concrete syntax (P4 or C) *)
  | Sexps    (* s-expression format *)
  | Coq      (* .v file *)
  | Ocaml    (* .ml file *)

type output =
  { out_file: Filename.t;
    out_fmt: fmt }

type 'a cfg =
  | Skip
  | Run of 'a

let is_skip : 'a cfg -> bool =
  function
  | Skip -> true
  | _ -> false

let cfg_of_bool : bool -> unit cfg =
  function
  | false -> Skip
  | true  -> Run ()

type pass_cfg =
  (output option) cfg

type parser_cfg =
  { cfg_infile: Filename.t;
    cfg_includes: Filename.t list;
    cfg_verbose: bool; }

type checker_cfg =
  { cfg_parser: parser_cfg;
    cfg_p4surface: pass_cfg;
    cfg_gen_loc: unit cfg;
    cfg_normalize: unit cfg;
    cfg_p4light: pass_cfg; }

type backend =
  | GCLBackend of {depth: int; gcl_output: output}
  | CBackend of output
  | TblBackend

type backend_cfg = backend cfg

type compiler_cfg =
  { cfg_checker: checker_cfg;
    cfg_p4cub: pass_cfg;
    cfg_p4flat: pass_cfg;
    cfg_backend: backend_cfg; }

type input_cfg =
  | InputSTF of Filename.t
  | InputPktPort of { input_pkt_hex: string;
                      input_port: int; }

type interpreter_cfg =
  { cfg_checker: checker_cfg;
    cfg_inputs: input_cfg; }

type cmd_cfg =
  | CmdParse of parser_cfg
  | CmdCheck of checker_cfg
  | CmdCompile of compiler_cfg
  | CmdInterp of interpreter_cfg

let parse_extension (ext: string) : fmt option =
  match ext with
  | "p4surface"
  | "p4light"
  | "p4cub"
  | "p4flat"
  | "gcl" -> Some Sexps
  | "p4"  -> Some Concrete
  | "ml"  -> Some Ocaml
  | "v"   -> Some Coq
  | _     -> None

let parse_output (out_file : Filename.t) : output option =
  let open Option.Let_syntax in
  let%bind ext = Filename.split_extension out_file |> snd in
  let%map out_fmt = parse_extension ext in
  {out_file; out_fmt}

let parse_output_exn (out_file : Filename.t) : output =
  match parse_output out_file with
  | Some o -> o
  | None -> failwith ("bad extension on filename: " ^ out_file)

let mk_parse_only include_dirs in_file : parser_cfg =
  { cfg_infile = in_file;
    cfg_includes = include_dirs;
    cfg_verbose = false }

let mk_check_only include_dirs in_file : checker_cfg =
  { cfg_parser = mk_parse_only include_dirs in_file;
    cfg_p4surface = Run None;
    cfg_gen_loc = Run ();
    cfg_normalize = Run ();
    cfg_p4light = Run None; }
