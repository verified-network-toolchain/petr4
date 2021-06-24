Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Require Import Poulet4.Bitwise.


Require Import Poulet4.P4cub.BigStep.Value.
Require Import Poulet4.P4cub.Syntax.P4Field.

Require Import Poulet4.P4automata.P4automaton.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Import Val.

Definition to_val (w: positive) (bs: list bool) : v :=
  let v := to_nat bs in
  VBit w (Z.of_nat v).

  
(* tuple of n bytes *)

Definition byte := {n: nat | n < 256 }.

Definition bits_to_nat (x: list bool) : {n: nat | n < 2^ length x}. 
induction x.
  - refine (exist _ 0 _).
    simpl.
    lia.
  - destruct IHx.
    destruct a.
    * refine (exist _ (x0 * 2) _).
      simpl.
      lia.
    * refine (exist _ x0 _).
      simpl.
      lia.
Defined.

Definition bits_8_to_byte (x: list bool) (pf: length x <= 8) : byte.
Admitted.

Fixpoint bytes (n : nat) : Type := 
  match n with 
  | 0 => unit
  | S n' => byte * bytes n'
  end.

Definition bs_idx {n} (bs: bytes (S n)) (i : nat) (pf: i <= (S n)) : byte.
induction i.
destruct bs.
- exact b.
- eapply IHi.
  lia.
Defined.

Definition slice {A} to from (l: list A) := firstn (from - to) (skipn to l).

Definition to_entry (bs: list bool) : v :=
  let entries :=
    ("label", to_val 20 (slice 0 20 bs)) ::
    ("class", to_val 3 (slice 20 23 bs)) ::
    ("bos_marker", to_val 1 (slice 23 24 bs)) ::
    ("ttl", to_val 8 (slice 24 32 bs)) ::
    nil in
  VHeader entries true.

Module TPP.
  Inductive states :=
  | parse_ip
  | parse_udp
  | parse_tpp_header
  | parse_tpp_instr
  | parse_tpp_memory
  | parse_suffix.

  Definition size' (s: states) : nat :=
    match s with
    | parse_ip => 6*8 (* 8 bytes for src/dest, 2 for protocol *)
    | parse_udp => 2*8 (* 2 bytes for dest port *)
    | parse_tpp_header => 8*8 (* 8 bytes in total *)
    | parse_tpp_instr => 8 (* 4 bytes per instruction, parse byte-by-byte *)
    | parse_tpp_memory => 8 (* parse memory byte-by-byte *)
    | parse_suffix => 2*8 (* 2 byte proto trailer *)
    end.

  Record ip := mkIP {
    source : bytes 4 ;
    dest : bytes 4;
    proto: bytes 2;
  }.

  Record udp := mkUDP {
    dest_port : byte ; 
    inner_len : byte ;
  }.

  Record tpp_header := mkTPPHeader {
    instr_len : nat;
    mem_len : nat;
    addr_mode: nat;
    sp : nat;
    phmem_len : nat;
  }.

  Definition operand := byte.
  
  Inductive tpp_instr := 
  | TPPload (r: operand) (l: operand)
  | TPPstore (l: operand) (r: operand) 
  | TPPpush (x: operand)
  | TPPpop (x: operand)
  | TPPcondstore (x: operand) (x': operand) (v: operand)
  | TPPcexec (addr: operand) (mask: operand).

  Definition tpp_mem := list byte.
  
  Record tpp_store := mkTPPStore {
    hdr: tpp_header;
    app_id : bytes 4;
    instrs : list tpp_instr;
    pkt_mem : tpp_mem;
  }.

  Record store := mkStore {
    ip_hdr : ip; 
    udp_hdr : udp; 
    tpp: option tpp_store;
  }.

(* 
  Program Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) => v
      <| entries ::= fun x => x ++ [(to_entry bs)] |>
      <| length ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) =>
      if v.(length) <? 4
      then inl parse_entry
      else inr false
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed. *)

End TPP.