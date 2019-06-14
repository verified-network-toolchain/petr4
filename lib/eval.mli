module I = Info
module Info = I (* JNF: ugly hack *)

val eval: Types.program -> unit

val eval_expression: Env.EvalEnv.t -> Types.Expression.t -> Value.t
