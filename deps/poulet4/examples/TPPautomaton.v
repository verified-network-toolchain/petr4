Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Require Import Poulet4.Bitwise.

Require Import Poulet4.Monads.Option.

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

Lemma slice_n_n' : 
  forall {A} (l : list A) n n', 
  length (slice n n' l) <= (n' - n). 
Admitted.

Fixpoint snoc {A} (x: A) (xs: list A) : list A :=
  match xs with 
  | nil       => x :: nil
  | x' :: xs' => x' :: (snoc x xs')
  end.


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
    | parse_tpp_instr => 4*8 (* 4 bytes per instruction, parse byte-by-byte *)
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
  (* | TPPpush (x: operand)
  | TPPpop (x: operand) *)
  | TPPcondstore (x: operand) (x': operand) (v: operand)
  | TPPcexec (addr: operand) (mask: operand).

  Definition tpp_mem := list byte.

  Definition tpp_program := (tpp_instr * list tpp_instr)%type.

  Inductive tpp_sec_label := TSHigh | TSLow .

  Scheme Equality for tpp_sec_label.

  Definition tsed := tpp_sec_label_eq_dec.
  
  Definition sec_typ_env := operand -> tpp_sec_label.

  Definition tpp_check_instr (env: sec_typ_env) (i: tpp_instr) := 
    match i with 
    | TPPload r l
    | TPPstore l r 
    | TPPcexec l r =>
      if tsed (env l) (env r) then Some (env l) else None
    (* | TPPpush x
    | TPPpop x => 
      if tsed (env x) (env sp) then Some (env x) else None *)
    | TPPcondstore x x' v => 
      if tsed (env x) (env x') 
      then if tsed (env x') (env v) 
      then Some (env x) else None
      else None
    end.
  
  Program Fixpoint tpp_check_prog (env: sec_typ_env) (branch: option tpp_sec_label) (prog: tpp_program) {measure (length (snd prog))} : option tpp_sec_label :=
    let '(nxt, instrs) := prog in 
    match instrs with 
    | nil             => tpp_check_instr env nxt
    | nxt' :: instrs' => 
      match branch with 
      | Some l => 
        let* r := tpp_check_instr env nxt in 
        if tsed l r
        then tpp_check_prog env branch (nxt', instrs')
        else None
      | None => 
        match nxt with 
        | TPPcondstore _ _ _
        | TPPcexec _ _ => 
          let* branch' := tpp_check_instr env nxt in 
          tpp_check_prog env (Some branch') (nxt', instrs')
        | _ => tpp_check_prog env branch (nxt', instrs')
        end
      end
    end.
    Solve All Obligations with (split; vm_compute; intros; congruence).

  Inductive instr_state := init.

  Record tpp_instr_store := mkInstrStore {
    prog : tpp_program;
  }.

  Definition prog_len (p: tpp_program) := 1 + length (snd p).

  Program Definition tpp_instr_twopass_parser 
    (parse_instr : bytes 4 -> option tpp_instr)
    (policy: operand -> tpp_sec_label)
    (amount: nat)
    : p4automaton := {|
      size := fun _ => 4 * 8;
      update := fun _ bs (st : tpp_instr_store) => 
        let opcode := bits_8_to_byte (slice 0 8 bs) _ in 
        let o1 := bits_8_to_byte (slice 8 16 bs) _ in 
        let o2 := bits_8_to_byte (slice 16 24 bs) _ in 
        let o3 := bits_8_to_byte (slice 24 32 bs) _ in 
        let instr := parse_instr (opcode, (o1, (o2, (o3, tt)))) in 
        match instr with 
        | None => st
        | Some i => 
          let '(oldi, oldis) := prog st in 
          {| prog := (i, snoc oldi oldis); |}
        end;
      transitions := fun _ st =>
        if prog_len (prog st) == amount then
          if tpp_check_prog policy None (prog st) 
          then inr true
          else inr false
        else inl init;
    |}.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    lia.
    Qed.
  

End TPP.