Require Export Poulet4.P4cub.Utiliser.
Require Export Poulet4.Platform.Packet.
Require Export Poulet4.Monads.State.
Require Poulet4.Environment.Environment.
Module EXN := Poulet4.Environment.Environment.
(* TODO: why is [exception] defined in [EXN]? *)
Require Import Coq.PArith.BinPosDef.
Require Import Coq.Strings.String.

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

(** State Monad for [t] *)
Definition paquet_monad : Type -> Type := @state_monad t EXN.exception.

(** Lift from [packet_monad] to [paquet_monad] *)
Definition lyft_inc
           {R : Type} (m : packet_monad R) : paquet_monad R :=
  fun pkt =>
    let '(RE, new_inc) := m $ incoming pkt in
    (RE,
     {| incoming := new_inc;
        emit_buffer := emit_buffer pkt;
        in_length := in_length pkt |}).
(**[]*)

Module Type P4Packet.
  (** P4 types. *)
  Parameter T : Type.

  (** P4 expression/value data type. *)
  Parameter E : Type.

  (** L-value data-type. *)
  Parameter LV : Type.

  (** Read from the packet. *)
  Parameter read : T -> paquet_monad E.

  (** Write to the packet. *)
  Parameter write : E -> t -> t.
End P4Packet.

(** P4cub Small-Step values *)
(*Module ExprPacket <: P4Packet.
  Definition T := E.t.

  (** A structure-preserving mapping [unit -> tags_t]
      may be written later. *)
  Definition E := E.e unit.

  Fixpoint read_inc (τ : E.t) : packet_monad (E.e unit) :=
    let read_field (fld : F.f string E.t)
        : packet_monad (F.f string (E.t * E.e unit)) :=
        let '(x,τ) := fld in
        e <<| read_inc τ ;; (x, (τ, e)) in
    match τ with
    | {{ Bool }} =>
      vec <<| read_first_bits 1 ;;
      E.EBool (Vector.hd vec) tt
    | {{ bit<w> }} =>
      let width := Pos.to_nat w in
      vec <<| read_first_bits width ;;
      E.EBit w (convert_bits width vec) tt
    | {{ int<w> }} =>
      let width := Pos.to_nat w in
      vec <<| read_first_bits width ;;
      E.EInt w (convert_bits width vec) tt
    | {{ rec { ts } }}
      => fs <<| sequence $ List.map read_field ts ;;
        <{ rec { fs } @ tt }>
    | {{ hdr { ts } }}
      => fs <<| sequence $ List.map read_field ts ;;
        <{ hdr { fs } valid:=TRUE @ tt @ tt }>
    | _ => state_fail
            $ EXN.TypeError "Unsupported type passed to extract."
    end.
  (**[]*)

  Definition read (τ : E.t) : paquet_monad (E.e unit) :=
    lyft_inc $ read_inc τ.
  (**[]*)

  Definition write (e : E.e unit) (pkt : t) : t :=
    {| incoming := incoming pkt;
       emit_buffer := emit_buffer pkt; (* TODO *)
       in_length := in_length pkt |}.    
End ExprPacket.*)
