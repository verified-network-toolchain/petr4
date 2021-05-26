Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.P4Packet.Paquet.
Require Export Poulet4.P4cub.P4Packet.PacketIn.
Require Import Coq.PArith.BinPos.
Require Import Coq.Strings.String.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.P4cub.Architecture.
Require Import BSUtil.
Require Import Value.
Module V := Val.
Import V.ValueNotations.
Import P4cub.P4cubNotations.
Module P := P4cub.

(** P4cub Big-Step values *)
Module ValuePacket <: P4Packet.
  Definition T := E.t.

  Definition E := V.v.

  Definition LV := V.lv.

  Fixpoint read_inc (τ : E.t) : packet_monad V.v :=
    let read_field (fld : F.f string E.t)
        : packet_monad (F.f string V.v) :=
        let '(x,τ) := fld in
        v <<| read_inc τ ;; (x, v) in
    match τ with
    | {{ Bool }} =>
      vec <<| read_first_bits 1 ;;
      V.VBool $ Vector.hd vec
    | {{ bit<w> }} =>
      let width := Pos.to_nat w in
      vec <<| read_first_bits width ;;
      V.VBit w $ convert_bits width vec
    | {{ int<w> }} =>
      let width := Pos.to_nat w in
      vec <<| read_first_bits width ;;
      V.VInt w $ convert_bits width vec
    | {{ rec { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ REC { vs } }~
    | {{ hdr { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ HDR { vs } VALID:=true }~
    | _ => state_fail
            $ EXN.TypeError "Unsupported type passed to extract."
    end.
  (**[]*)
  
  Definition read (τ : E.t) : paquet_monad V.v :=
    lyft_inc $ read_inc τ.
  (**[]*)
  
  Definition write (v : V.v) (pkt : t) : t :=
    {| incoming := incoming pkt;
       emit_buffer := emit_buffer pkt; (* TODO *)
       in_length := in_length pkt |}.
End ValuePacket.

Module ARCH := Arch ValuePacket.

Module BSPacketIn <: P4PacketIn.
  Include ValuePacket.
  
  (** [packet_in.extract] *)
  Definition p4extract (τ : E.t) (lv : Val.lv) (ϵ : EnvUtil.epsilon)
  : PKT.paquet_monad EnvUtil.epsilon :=
    v <<| ValuePacket.read τ ;; EnvUtil.lv_update lv v ϵ.
  (**[]*)

  Definition dispatch_method
             (method: string)
             '(P.Arrow args lv : P.arrow string (E.t * V.v) (E.t * V.lv) (E.t * V.lv))
             (ϵ : EnvUtil.epsilon)
    : PKT.paquet_monad EnvUtil.epsilon :=
    match method,args,lv with
    | "length", [], Some (_,lv)
      => fun pkt => state_return
                  (EnvUtil.lv_update
                     lv (V.VBit 32%positive $ PacketIn.length pkt) ϵ) pkt
    | "advance", [("sizeInBits", P.PAIn (_, ~{ _ VW n }~))], None
      => fun pkt => state_return ϵ (PacketIn.advance n pkt)
    | "extract", [("hdr", P.PAOut (τ, lv))], None => p4extract τ lv ϵ
    | _,_,_ => state_fail PKT.EXN.Internal
    end.
End BSPacketIn.

Definition PacketIn : ARCH.P4Extern :=
  {| ARCH.dispatch_method := BSPacketIn.dispatch_method |}.
