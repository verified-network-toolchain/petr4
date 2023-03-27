open Core

type error
val error_to_string : error -> string
val handle_error : ('a, error) Result.t -> 'a

module type DriverIO = sig
  val red: string -> string
  val green: string -> string
  val preprocess: Filename.t list -> Filename.t -> string
  val open_file: Filename.t -> Out_channel.t
  val close_file: Out_channel.t -> unit
end

module MakeDriver (IO : DriverIO) : sig
  val run_parser : Pass.parser_cfg -> (Surface.program, error) Result.t
  val run_checker : Pass.checker_cfg -> (P4light.program, error) Result.t
  val run_interpreter : Pass.interpreter_cfg -> (unit, error) Result.t
  val run_compiler : Pass.compiler_cfg -> (unit, error) Result.t
  val run : Pass.cmd_cfg -> (unit, error) Result.t
end
val run_tbl : unit -> unit
