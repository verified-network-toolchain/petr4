module I = Info
module Info = I (* JNF: ugly hack *)
open Value
open Env
open Types

type value = EvalEnv.t pre_value

val eval: program -> unit
val eval_expression: EvalEnv.t -> Expression.t -> value
