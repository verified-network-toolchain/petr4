Set Warnings "-custom-entry-overridden".
From Coq Require Import PArith.BinPos
     NArith.BinNat Strings.String.
From Poulet4 Require Import P4cub.Syntax.CubNotations.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     Architecture.Paquet
     Architecture.PacketIn
     Architecture.Architecture
     BigStep.ValEnvUtil BigStep.Value.Syntax.
Module V := Val.
Import AllCubNotations V.ValueNotations.
Open Scope string_scope.

(** P4cub Big-Step values *)
Module ValuePacket <: P4Packet.
  Definition T := Expr.t.

  Definition E := V.v.

  Definition LV := V.lv.

  Definition convert_bits : list bool -> Z.
  Admitted.

  Fixpoint read_inc (τ : Expr.t) : Packet V.v :=
    let read_field (fld : F.f string Expr.t)
        : Packet (F.f string V.v) :=
        let '(x,τ) := fld in
        v <<| read_inc τ ;; (x, v) in
    match τ with
    | {{ Bool }} =>
      b <<| extract_bit ;;
      V.VBool b
    | {{ bit<w> }} =>
      let width := N.to_nat w in
      bs <<| extract_bits width ;;
      V.VBit w $ convert_bits bs
    | {{ int<w> }} =>
      let width := Pos.to_nat w in
      bs <<| extract_bits width ;;
      V.VInt w $ convert_bits bs
    | {{ struct { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ STRUCT { vs } }~
    | {{ hdr { ts } }}
      => vs <<| sequence $ List.map read_field ts ;;
        ~{ HDR { vs } VALID:=true }~
    | _ => state_fail
            $ TypeError "Unsupported type passed to extract."
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
    | _,_,_ => state_fail (TypeError "nonexistent method invoked")
    end.
End BSPacketIn.

Definition PacketIn (ϵ : epsilon) : ARCH.P4Extern :=
  {| ARCH.closure := ϵ;
     ARCH.dispatch_method := BSPacketIn.dispatch_method |}.
(**[]*)
