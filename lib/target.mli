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

  type st = obj State.t

  type 'st extern = ('st, st) pre_extern

  val externs : (string * st extern) list

  val eval_extern : st assign -> ctrl -> EvalEnv.t -> st -> Type.t list ->
                    value list -> string -> EvalEnv.t * st * signal * value

  val check_pipeline : EvalEnv.t -> unit 

  val eval_pipeline : ctrl -> EvalEnv.t -> st -> pkt -> Bigint.t ->
  (ctrl -> EvalEnv.t -> st -> signal -> value -> Argument.t list -> EvalEnv.t * st * signal * 'a) -> 
  st assign -> 
  (ctrl -> EvalEnv.t -> st -> string -> Type.t -> value) -> st * EvalEnv.t * pkt

end

module V1Model : Target

module EbpfFilter : Target