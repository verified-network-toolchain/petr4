module I = Info
module Info = I (* JNF: ugly hack *)
open Value
open Env
open Types

val eval_program: program -> unit
val eval_expression: EvalEnv.t -> Expression.t -> EvalEnv.t * value
