module I = Info
module Info = I (* JNF: ugly hack *)
open Types
open Value
open Target

type env = Env.EvalEnv.t

module type Interpreter = sig

  type state

  val empty_state : state

  val eval : ctrl -> env -> state -> pkt -> Bigint.t -> state * env * pkt

  val eval_decl : ctrl -> env -> state -> Declaration.t -> (env * state)

  val eval_statement : ctrl -> env -> state -> Statement.t -> (env * state)

  val eval_expression : ctrl -> env -> state -> Expression.t -> (env * state * value)

  val eval_app : ctrl -> env -> state -> signal -> value -> Argument.t list -> env * state * signal * value

  val eval_assign' : ctrl -> env -> state -> lvalue -> value -> env * state * signal

  val init_val_of_typ : ctrl -> env -> state -> string -> Type.t -> value

end

module MakeInterpreter : functor (T : Target) -> Interpreter

module V1Interpreter : Interpreter

(* module EbpfInterpreter : Interpreter *)

val eval_prog : program -> ctrl -> pkt -> Bigint.t -> (string * Bigint.t) option
