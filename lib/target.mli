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
  type 'a t

  val empty : 'a t

  val packet_location : loc

  val fresh_loc : unit -> loc

  val get_packet : 'a t -> pkt
  val set_packet : pkt -> 'a t -> 'a t
  val insert_extern : loc -> 'a -> 'a t -> 'a t
  val find_extern : loc -> 'a t -> 'a
  val insert_heap : loc -> value -> 'a t -> 'a t
  val find_heap : loc -> 'a t -> value
  val is_initialized : loc -> 'a t -> bool
end

type 'a writer = 'a State.t -> bool -> (string * loc) list -> string -> value -> 'a State.t

type 'a reader = 'a State.t -> bool -> (string * loc) list -> string -> value

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern : 
    string -> ctrl -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt -> state apply -> state * env * pkt option

end

val width_of_typ : env -> Type.t -> Bigint.t

val init_val_of_typ : 'a State.t -> env -> Type.t -> 'a State.t * value

val width_of_val : 'a State.t -> value -> Bigint.t

val implicit_cast_from_rawint : env -> value -> Type.t -> value

val implicit_cast_from_tuple : 'a State.t -> env -> value -> Type.t -> 'a State.t * value

val implicit_cast : 'a State.t -> env -> value -> Type.t -> 'a State.t * value

val value_of_lvalue : 'a reader -> 'a State.t -> env -> lvalue -> signal * value

val assign_lvalue : 'a reader -> 'a writer -> 'a State.t -> env -> lvalue -> value -> bool -> 'a State.t * env * signal
