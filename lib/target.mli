open Typed
open Prog

type env = Eval_env.t

type 'st pre_extern =
  env -> 'st -> coq_P4Type list -> (coq_Value * coq_P4Type) list ->
  env * 'st * signal * coq_Value

type 'st apply =
  ctrl -> env -> 'st -> signal -> coq_Value -> coq_Expression option list -> 'st * signal * coq_Value

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
  val insert_heap : loc -> coq_Value -> 'a t -> 'a t
  val find_heap : loc -> 'a t -> coq_Value
  val is_initialized : loc -> 'a t -> bool
end

type 'a writer = bool -> (string * coq_Value) list -> string -> coq_Value -> coq_Value

type 'a reader = bool -> (string * coq_Value) list -> string -> coq_Value

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern : 
    string -> env -> state -> coq_P4Type list -> (coq_Value * coq_P4Type) list ->
    env * state * signal * coq_Value

  val initialize_metadata : Bigint.t -> state -> state

  val check_pipeline : env -> unit 

  val eval_pipeline : ctrl -> env -> state -> pkt -> state apply -> state * env * pkt option

  val get_outport : state -> env -> Bigint.t

end

val width_of_typ : env -> coq_P4Type -> Bigint.t

val init_val_of_typ : env -> coq_P4Type -> coq_Value

val width_of_val : coq_Value -> Bigint.t

val value_of_lvalue : 'a reader -> env -> 'a State.t -> coq_ValueLvalue -> signal * coq_Value

val assign_lvalue : 'a reader -> 'a writer -> 'a State.t -> env -> coq_ValueLvalue -> coq_Value -> 'a State.t * signal
