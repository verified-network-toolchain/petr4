module I = Info
module Info = I (* JNF: ugly hack *)
open Prog
open Typed
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

  val eval_app : ctrl -> env -> state -> signal -> value -> Expression.t option list -> env * state * signal * value

  val eval_assign' : env -> lvalue -> value -> env * signal

  val init_val_of_typ : Type.t -> value

end

module MakeInterpreter : functor (T : Target) -> Interpreter

module V1Interpreter : Interpreter

(* module EbpfInterpreter : Interpreter *)

val eval_prog : program -> ctrl -> pkt -> Bigint.t -> (string * Bigint.t) option
