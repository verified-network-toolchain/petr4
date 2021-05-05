Require Import Poulet4.P4cub.Utiliser.
Require Import Poulet4.Platform.Packet.

(** * Blackbox Module For P4 Packet API *)

(** Data-type for packet. *)
Record t : Set :=
  { incoming: list bool; emit_buffer: list bool; in_length: nat }.
(**[]*)

(** Packet length. *)
Definition size (pkt : t) : nat := in_length pkt.

(** Consume the packet by [n] bits. *)
Definition consume_incoming (n : nat) (pkt : t) : t :=
  {| incoming := List.skipn n $ incoming pkt;
     emit_buffer := emit_buffer pkt;
     in_length := in_length pkt |}.
(**[]*)

Module Type P4Packet.
  (** P4 types. *)
  Parameter T : Type.

  (** P4 expression/value data type. *)
  Parameter E : Type.

  (** Read from the packet. *)
  Parameter read : t -> T -> E.

  (** Write to the packet. *)
  Parameter write : E -> t -> t.
End P4Packet.
