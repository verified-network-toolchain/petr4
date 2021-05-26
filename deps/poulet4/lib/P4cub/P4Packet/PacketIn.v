(** * The P4 Core [packet_in] Extern *)

Require Import Poulet4.P4cub.Envn.
Require Paquet.
Module PKT := Paquet.
(* TODO: helpers need a different file from semantics. *)
Require Import Coq.ZArith.BinIntDef.
Require Import Poulet4.P4cub.Utiliser.

(** [packet_in.advance] *)
Definition advance (sizeInBits : Z) (pkt : PKT.t) : PKT.t :=
  PKT.consume_incoming (Z.to_nat sizeInBits) pkt.
(**[]*)

(** [packet_in.length] *)
Definition length : PKT.t -> Z := Z.of_nat ∘ PKT.in_length.

Module Type P4PacketIn.
  Include PKT.P4Packet.

  Parameter p4extract : T -> LV -> Env.t string E -> PKT.paquet_monad (Env.t string E).
End P4PacketIn.
