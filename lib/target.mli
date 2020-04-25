open Value
open Env
open Types

type extern = EvalEnv.t -> value list -> EvalEnv.t * value 

module type Target = sig 

  type st

  val dummy_st : st

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  (ctrl -> EvalEnv.t -> st -> lvalue -> value -> EvalEnv.t * st * 'b) -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

module Core : Target 

module V1Model : Target

module EbpfFilter : Target