open Value
open Env
open Types

module type target = sig 
  type extern = EvalEnv.t -> value list -> EvalEnv.t * value 

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : EvalEnv.t -> packet_in -> 
  (EvalEnv.t -> signal -> value -> Argument.t list -> EvalEnv.t * signal * 'a) -> 
  (EvalEnv.t -> lvalue -> value -> EvalEnv.t * 'b) -> packet_in

end

module Core : target 

module V1Model : target