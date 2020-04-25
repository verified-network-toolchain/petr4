module I = Info
module Info = I (* JNF: ugly hack *)
open Types
open Value
open Target

type env = Env.EvalEnv.t

module type Interpreter = sig

  type st

  val dummy_st : st

  val eval : ctrl -> env -> st -> pkt -> (st * pkt)

  val eval_decl : ctrl -> env -> st -> Declaration.t -> (env * st)

  val eval_statement : ctrl -> env -> st -> pkt -> Statement.t -> (env * st * pkt)

  val eval_expression : ctrl -> env -> st -> pkt -> Expression.t -> (env * st * pkt * value)

  val eval_app : ctrl -> env -> st -> signal -> value -> Argument.t list -> env * st * signal * value

  val eval_assign' : ctrl -> env -> st -> lvalue -> value -> env * st * signal

  val init_val_of_typ : ctrl -> env -> st -> string -> Type.t -> value

end

module MakeInterpreter : functor (T : Target) -> Interpreter

val eval_prog : program -> ctrl -> pkt -> string
