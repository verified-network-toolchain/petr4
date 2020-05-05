open Typed
open Prog
open Value
open Env

type env = EvalEnv.t

type 'st pre_extern =
  ctrl -> env -> 'st -> Type.t list -> (value * Type.t) list ->
  env * 'st * signal * value

type 'st apply =
  ctrl -> env -> 'st -> signal -> value -> Expression.t option list -> env * 'st * signal * value

module State : sig
  type 'a t = (string * 'a) list

  val packet_location : loc

  val empty : 'a t
  val insert : loc -> 'a -> 'a t -> 'a t
  val find : loc -> 'a t -> 'a
  val is_initialized : loc -> 'a t -> bool
end

module type Target = sig 

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val eval_extern : 
    string -> ctrl -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt -> state apply -> state * env * pkt

end

(* module type Core = sig
  include Target

  val make_pkt_in : pkt -> obj

  val make_pkt_out : pkt -> pkt -> obj

  val assert_pkt_in : obj -> pkt

  val assert_pkt_out : obj -> pkt * pkt

end *)

val init_val_of_typ : env -> Type.t -> value

val implicit_cast_from_rawint : env -> value -> Type.t -> value

val implicit_cast_from_tuple : env -> value -> Type.t -> value

val value_of_lvalue : env -> lvalue -> signal * value

val assign_lvalue : env -> lvalue -> value -> env * signal

(* module Core : Core *)

(* module Corize : functor Target -> Target *)
