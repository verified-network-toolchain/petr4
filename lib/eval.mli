module I = Info
module Info = I (* JNF: ugly hack *)
open Env
open Types
open P4core

val eval_program: program -> unit
val eval_expression: EvalEnv.t -> Expression.t -> EvalEnv.t * value
