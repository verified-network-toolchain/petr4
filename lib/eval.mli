module I = Info
module Info = I (* JNF: ugly hack *)
open Value
open Env
open Types

val eval: program -> unit
val eval_expression: EvalEnv.t -> Expression.t -> value
