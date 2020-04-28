open Value
open Env
open Types

type 'st assign = 
  ctrl -> EvalEnv.t -> 'st -> lvalue -> value -> EvalEnv.t * 'st * signal

type ('st1, 'st2) pre_extern =
  'st1 assign -> ctrl -> EvalEnv.t -> 'st2 -> Type.t list -> value list ->
  EvalEnv.t * 'st2 * signal * value

module State : sig
  type 'a t

  val empty : 'a t
  val insert : int -> 'a -> 'a t -> 'a t
  val find : int -> 'a t -> 'a
  val fresh_loc : unit -> int
end

module type Target = sig 

  type obj

  type state = obj State.t

  type 'st extern = ('st, state) pre_extern

  val externs : (string * state extern) list

  val eval_extern : state assign -> ctrl -> EvalEnv.t -> state -> Type.t list ->
                    value list -> string -> EvalEnv.t * state * signal * value

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : ctrl -> EvalEnv.t -> state -> pkt -> Bigint.t ->
  (ctrl -> EvalEnv.t -> state -> signal -> value -> Argument.t list -> EvalEnv.t * state * signal * 'a) -> 
  state assign -> 
  (ctrl -> EvalEnv.t -> state -> string -> Type.t -> value) -> state * EvalEnv.t * pkt

end

module V1Model : Target

module EbpfFilter : Target