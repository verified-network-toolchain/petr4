Set Warnings "-custom-entry-overridden".
From Coq Require Import PArith.BinPos
     NArith.BinNat Strings.String.
From Poulet4.P4cub Require Import
     Architecture.Paquet
     Architecture.PacketIn Envn
     Architecture.Architecture
     BigStep.ValEnvUtil BigStep.Value.Syntax
     Syntax.CubNotations.
Module V := Val.
Import AllCubNotations V.ValueNotations.

(** P4cub Big-Step values *)
Module ValuePacket <: P4Packet.
  Definition T := Expr.t.

  Definition E := V.v.

  Definition LV := V.lv.

  Fixpoint read_inc (τ : Expr.t) : packet_monad V.v :=
    let read_field (fld : F.f string Expr.t)
        : packet_monad (F.f string V.v) :=
        let '(x,τ) := fld in
        v <<| read_inc τ ;; (x, v) in
    match τ with
    | {{ Bool }} =>
      vec <<| read_first_bits 1 ;;
      V.VBool $ Vector.hd vec
    | {{ bit<w> }} =>
      let width := N.to_nat w in
      vec <<| read_first_bits width ;;
      V.VBit w $ convert_bits width vec
    | {{ int<w> }} =>
      let width := Pos.to_nat w in
      vec <<| read_first_bits width ;;
      V.VInt w $ convert_bits width vec
    | {{ struct { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ STRUCT { vs } }~
    | {{ hdr { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ HDR { vs } VALID:=true }~
    | _ => state_fail
            $ EXN.TypeError "Unsupported type passed to extract."
    end.
  (**[]*)
  
  Definition read (τ : Expr.t) : paquet_monad V.v :=
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
  Definition p4extract (τ : Expr.t) (lv : Val.lv) (ϵ : epsilon)
    : PKT.paquet_monad epsilon :=
    v <<| ValuePacket.read τ ;; lv_update lv v ϵ.
  (**[]*)

  Definition dispatch_method
             (method: string)
             '({|paramargs:=args; rtrns:=lv|} : arrow string V.v V.lv V.lv)
             (ϵ : epsilon)
    : PKT.paquet_monad epsilon :=
    match method,args,lv with
    | "length", [], Some lv
      => fun pkt => state_return
                  (lv_update
                     lv (V.VBit 32%N $ PacketIn.length pkt) ϵ) pkt
    | "advance", [("sizeInBits", PAIn (~{ _ VW n }~))], None
      => fun pkt => state_return ϵ (PacketIn.advance n pkt)
    | "extract", [("hdr", PAOut lv)], None => p4extract {{ Bool }} lv ϵ (* TODO: fix *)
    | _,_,_ => state_fail PKT.EXN.Internal
    end.
End BSPacketIn.

Definition PacketIn (ϵ : epsilon) : ARCH.P4Extern :=
  {| ARCH.closure := ϵ;
     ARCH.dispatch_method := BSPacketIn.dispatch_method |}.
(**[]*)
