module I = Info
module Info = I (* JNF: ugly hack *)
open Env
open Types
open Value

val eval_program: program -> packet_in -> Table.pre_entry list -> Match.t list list -> string
val eval_expression: EvalEnv.t -> Expression.t -> EvalEnv.t * value
