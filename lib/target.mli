open Value
open Env
open Types

type extern = EvalEnv.t -> value list -> EvalEnv.t * value
(* 
module type State = sig
  type loc = int
  type 'a t
  val empty : 'a t
  val insert : loc -> 'a -> 'a t -> 'a t
  val find : loc -> 'a t -> 'a
  val fresh_loc : unit -> loc
end

module State : State *)

module type Target = sig 

  type obj
  type st

  val empty_state : st
  val insert : int -> obj -> st -> st
  val find : int -> st -> obj
  val fresh_loc : unit -> int

  val obj_mem : obj -> string -> value

  val externs : (string * extern) list

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> 
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  (ctrl -> EvalEnv.t -> st -> lvalue -> value -> EvalEnv.t * st * 'b) -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * pkt

end

(* module Core *)

module V1Model : Target

(* module EbpfFilter : Target *)