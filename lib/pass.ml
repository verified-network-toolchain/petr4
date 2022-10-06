open Core

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

type backend =
  | GCLBackend of {depth: int; gcl_output: output}
  | CBackend of output

type backend_cfg = backend cfg

type compiler_cfg =
  { cfg_infile: Filename.t;
    cfg_includes: Filename.t list;
    cfg_verbose: bool;
    cfg_p4surface: pass_cfg;
    cfg_gen_loc: unit cfg;
    cfg_normalize: unit cfg;
    cfg_p4light: pass_cfg;
    cfg_p4cub: pass_cfg;
    cfg_p4flat: pass_cfg;
    cfg_backend: backend_cfg; }

let parse_extension (ext: string) : fmt option =
  match ext with
  | ".p4surface"
  | ".p4light"
  | ".p4cub"
  | ".p4flat"
  | ".gcl"       -> Some Sexps
  | ".p4"        -> Some Concrete
  | ".ml"        -> Some Ocaml
  | ".v"         -> Some Coq
  | _            -> None

let parse_output (out_file : Filename.t) : output option =
  let open Option.Let_syntax in
  let%bind ext = Filename.split_extension out_file |> snd in
  let%map out_fmt = parse_extension ext in
  {out_file; out_fmt}

let parse_output_exn (out_file : Filename.t) : output =
  match parse_output out_file with
  | Some o -> o
  | None -> failwith ("bad extension on filename: " ^ out_file)

let mk_parse_only include_dirs in_file : compiler_cfg =
  failwith "mk_parse_only unimplemented"

let mk_check_only include_dirs in_file : compiler_cfg =
  failwith "mk_check_only unimplemented"
