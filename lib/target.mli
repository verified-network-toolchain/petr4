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

type writer = bool -> (string * value) list -> string -> value -> value

type reader = bool -> (string * value) list -> string -> value

module State : sig
  type 'a t

  val empty : 'a t

  val packet_location : loc

  val get_packet : 'a t -> pkt
  val set_packet : pkt -> 'a t -> 'a t
  val insert : loc -> 'a -> 'a t -> 'a t
  val find : loc -> 'a t -> 'a
  val filter : f:(loc * 'a -> bool) -> 'a t -> 'a t
  val map : f:('a -> 'b) -> 'a t -> 'b t
  val merge : 'a t -> 'a t -> 'a t
  val is_initialized : loc -> 'a t -> bool
end

module type Reader = sig
  val read_header_field : reader
end

module type Writer = sig
  val write_header_field : writer
end

module type Target = sig
  include Reader
  include Writer

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val externs : (string * extern) list

  val eval_extern : 
    string -> ctrl -> env -> state -> Type.t list -> (value * Type.t) list ->
    env * state * signal * value

  val initialize_metadata : Bigint.t -> env -> env

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt -> state apply -> state * env * pkt option

end

(* BasicReader and BasicWriter ignore the validity bit *)
module BasicReader : Reader
module BasicWriter : Writer

val width_of_typ : env -> Type.t -> Bigint.t

val init_val_of_typ : env -> Type.t -> value

val implicit_cast_from_rawint : env -> value -> Type.t -> value

val implicit_cast_from_tuple : env -> value -> Type.t -> value

val implicit_cast : env -> value -> Type.t -> value

val value_of_lvalue : reader -> env -> lvalue -> signal * value

val assign_lvalue : reader -> writer -> env -> lvalue -> value -> bool -> env * signal
