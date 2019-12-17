module I = Info
module Info = I (* JNF: ugly hack *)
open Env
open Types
open Value

val eval_program: program -> ctrl -> packet_in -> unit
val eval_expression: EvalEnv.t -> ctrl -> Expression.t -> EvalEnv.t * value
