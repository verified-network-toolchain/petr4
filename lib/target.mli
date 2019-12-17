open Value
open Env
open Types

type extern = EvalEnv.t -> value list -> EvalEnv.t * value 

module type Target = sig 

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : EvalEnv.t -> ctrl -> packet_in -> 
  (EvalEnv.t -> ctrl -> signal -> value -> Argument.t list -> EvalEnv.t * signal * 'a) -> 
  (EvalEnv.t -> ctrl -> lvalue -> value -> EvalEnv.t * 'b) -> 
  (EvalEnv.t -> ctrl -> string -> Type.t -> value) -> packet_in

end

module Core : Target 

module V1Model : Target

module EbpfFilter : Target