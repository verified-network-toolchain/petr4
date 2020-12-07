module I = Info
module Info = I (* JNF: ugly hack *)
open Prog
open Target

type env = Eval_env.t

module type Interpreter = sig

  (* the type of a state is unique to each interpreter instance *)
  type state

  val empty_state : state

  (** [eval_expression env st expr] is [st', v], where [v] is the value obtained
      from evaluating the P4 expression [expr] under the environment [env] and
      the state [st], and [st'] is [st] updated according to the side-effects of
      the same evaluation. *)
  val eval_expression : env -> state -> coq_Expression -> state * coq_Value

  (** [eval_statement ctrl env st stmt] is [env', st'], where [env'] is [env]
      updated with the bindings produced by evaluating [stmt] under the
      control-plane configuration [ctrl], environment [env], and state [st],
      and [st'] is [st] updated according to the side-effects of the same
      evaluation. *)
  val eval_statement : ctrl -> env -> state -> coq_Statement -> env * state

  (** [eval_declaration ctrl env st decl] is [env', st'], where [env'] is [env]
      updated with the bindings produced by evaluating [decl] under the
      control-plane configuration [ctrl], environment [env], and state [st],
      and [st'] is [st] updated according to the side-effects of the same
      evaluation. *)
  val eval_declaration : ctrl -> env -> state -> coq_Declaration -> env * state

  (** [eval_program ctrl env st pkt port prog] is [st', None] if [prog] drops
      the packet [pkt] with ingress port [port] under control-plane
      configuration [ctrl], environment [env], and state [st], producing the 
      side-effects in [st']. It is [st', Some (pkt', port')] if [prog] updates
      the packet [pkt] to [pkt'] and sends it out on egress port [port'] under
      control-plane configuration [ctrl], environment [env], and state [st],
      producing the side-effects in [st']. *)
  val eval_program : ctrl -> env -> state -> buf -> Bigint.t -> program ->
    state * (buf * Bigint.t) option

end

(** [MakeInterpreter(T)] is a P4 interpreter instantiated on the target [T]. *)
module MakeInterpreter : functor (T : Target) -> Interpreter

(** [V1Interpreter] is an interpreter for P4 under the V1model architecture. *)
module V1Interpreter : Interpreter

(** [EbpfInterpreter] is an interpreter for P4 under the eBPF architecture. *)
module EbpfInterpreter : Interpreter

(** [Up4Interpreter] is an interpreter for P4 under the uP4 architecture. *)
module Up4Interpreter : Interpreter
