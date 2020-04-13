open Value
open Env
open Types

(* type extern = EvalEnv.t -> value list -> EvalEnv.t * value *)

module State : sig
  type 'a t

  val empty : 'a t
  val insert : int -> 'a -> 'a t -> 'a t
  val find : int -> 'a t -> 'a
  val fresh_loc : unit -> int
end

module type Target = sig 

  type obj

  type st = obj State.t

  type extern = EvalEnv.t -> st -> value list -> EvalEnv.t * st * value

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  (ctrl -> EvalEnv.t -> st -> lvalue -> value -> EvalEnv.t * st * 'b) -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

module V1Model : Target

module EbpfFilter : Target