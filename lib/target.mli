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

val init_val_of_typ : env -> Type.t -> value

val implicit_cast_from_rawint : env -> value -> Type.t -> value

val implicit_cast_from_tuple : env -> value -> Type.t -> value

val value_of_lvalue : env -> lvalue -> signal * value

val assign_lvalue : env -> lvalue -> value -> env * signal

module State : sig
  type 'a t

  val packet_location : string

  val empty : 'a t

  val insert : loc -> 'a -> 'a t -> 'a t
  val find : loc -> 'a t -> 'a
  val filter : f:(loc * 'a -> bool) -> 'a t -> 'a t
  val map : f:('a -> 'b) -> 'a t -> 'b t
  val merge : 'a t -> 'a t -> 'a t
  val is_initialized : loc -> 'a t -> bool
  (* val fresh_loc : unit -> int *)
end

module type Target = sig 

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val eval_extern : ctrl -> env -> state -> Type.t list ->
                    (value * Type.t) list -> string -> env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply ->
  state * env * pkt

end
