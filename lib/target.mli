open Typed
open Prog
open Value
open Env

type env = EvalEnv.t

type 'st assign = env -> lvalue -> value -> env * signal

type ('st1, 'st2) pre_extern =
  'st1 assign -> ctrl -> env -> 'st2 -> Type.t list -> (value * Type.t) list ->
  env * 'st2 * signal * value

type 'st apply =
  ctrl -> env -> 'st -> signal -> value -> Expression.t option list -> env * 'st * signal * value

type 'st init_typ = 
  env -> Type.t -> value

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

  val eval_extern : state assign -> ctrl -> env -> state -> Type.t list ->
                    (value * Type.t) list -> string -> env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> 
  state assign -> 
  state init_typ -> state * env * pkt

end

module V1Model : Target

module EbpfFilter : Target
