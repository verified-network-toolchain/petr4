open Typed
open Prog
open Value
open Env

type env = EvalEnv.t

type 'st pre_extern = env -> 'st -> Type.t list -> (value * Type.t) list ->
                      env * 'st * signal * value

type 'st apply = ctrl -> env -> 'st -> signal -> value ->
                 Expression.t option list -> 'st * signal * value

module State : sig
  type 'a t

  val empty : 'a t

  val packet_location : loc

  val fresh_loc : unit -> loc

  val reset_state : 'a t -> 'a t

  val get_packet : 'a t -> pkt
  val set_packet : pkt -> 'a t -> 'a t
  val insert_extern : loc -> 'a -> 'a t -> 'a t
  val find_extern : loc -> 'a t -> 'a
  val insert_heap : loc -> value -> 'a t -> 'a t
  val find_heap : loc -> 'a t -> value
  val is_initialized : loc -> 'a t -> bool
  val merge : 'a t -> 'a t -> 'a t
end

type 'a writer = bool -> (string * value) list -> string -> value -> value

type 'a reader = bool -> (string * value) list -> string -> value

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern :
    string -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> Bigint.t -> state -> state

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt ->
                      state apply -> state * env * (pkt * Bigint.t) list

end

val width_of_typ : env -> Type.t -> Bigint.t

val init_val_of_typ : env -> Type.t -> value

val width_of_val : value -> Bigint.t

val value_of_lvalue : 'a reader -> env -> 'a State.t -> lvalue -> signal * value

val assign_lvalue : 'a reader -> 'a writer -> 'a State.t -> env -> lvalue ->
                    value -> 'a State.t * signal
