Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNatDef.

Require Import Poulet4.P4Arith.

Import ListNotations.

Open Scope bool_scope.
Open Scope nat_scope.

(* convenience functions for treating bits and nats as little-endian bitvectors *)

(* It would be nice to use Coq's Bvectors, but, dependently-typed vectors are a pain to work with.
   So instead we use a similar representation and expose options.
*)
Section Bitwise.
  Definition Bits := list bool.

  (* increment a bitvector *)
  Fixpoint incr (b: Bits) : Bits :=
    match b with
    | [] => []
    | true :: xs => false :: incr xs
    | false :: xs => true :: xs
    end.

  Definition zero (w: nat) : Bits := repeat false w.

  (* Much faster conversion *)
  Definition of_N (n : N) (w: nat)  :=
    let fix of_N' (n : N) (w : nat) :=
      match w with
      | O => []
      | S w' => (N.odd n) :: (of_N' (N.div2 n) w')
      end in
    of_N' (Z.to_N (BitArith.mod_bound (Pos.of_nat w) (Z.of_N n))) w.

  Fixpoint to_N (bits : Bits) : N := 
    match bits with 
    | [] => 0
    | h :: t => N.add (if h then 1 else 0) (N.mul 2 (to_N t))
    end.
  
  Definition of_nat (n: nat) (w: nat) := Nat.iter n incr (zero w).

  Fixpoint pow_two (w: nat) : nat :=
    match w with
    | 0     => 1
    | S w'  => Nat.double (pow_two w')
    end.

  Definition add_bit_carry (part_with_width : nat * nat) (bit: bool) : nat * nat :=
    let '(part, w) := part_with_width in
    match bit with
    | false =>  (part, w + 1)
    | true =>  (part + pow_two w, w + 1)
    end.

  Definition to_nat (bits: Bits) : nat := fst (fold_left add_bit_carry bits (0,0)).

  Lemma add_carry_zero : forall w k, 
    fst (fold_left add_bit_carry (zero w) (0, k)) = 0.
  Proof.
    intros w.
    induction w; intros k; induction k; auto.
    - apply IHw.
    - apply IHw.
  Qed.

  Lemma to_nat_zero: forall w, to_nat (zero w) = 0.
  Proof.
    intros.
    unfold to_nat.
    apply add_carry_zero.
  Qed.

  Lemma to_of_nat_corr : forall w n,
    n < pow_two n -> to_nat (of_nat n w) = n.
    Proof.
      intros.
      induction n.
        - apply to_nat_zero.
    Admitted.

  Definition slice (w: nat) (bits: Bits) (lo: nat) (hi: nat) : option Bits :=
    if (hi <? w) && (lo <=? hi) then
    Some (firstn (w - hi) (skipn lo bits)) else
    None.

  Definition splice (wl: nat) (lhs: Bits) (lo: nat) (hi: nat) (wr: nat) (rhs: Bits) : option Bits :=
    if (lo <=? hi) && (wr <=? (hi - lo + 1)) then
    let pref := firstn lo lhs in
    let suff := skipn (wl - hi + 1) lhs in
    Some (pref ++ rhs ++ suff) else
    None.

  (* Conversion with big-endian bit vectors *)
  Definition little_to_big (bits: Bits) : Bits := rev bits.

  Definition big_to_little (bits: Bits) : Bits := rev bits.

  Fixpoint map2 {A : Type} (f : A -> A -> A) (l1 : list A) (l2 : list A) : (list A) :=
    match l1, l2 with
    | [], _ => l2
    | _, []  => l1
    | h1 :: t1, h2 :: t2 => (f h1 h2) :: (map2 f t1 t2)
    end.

  Definition xor := map2 xorb.

End Bitwise.

(* Compute slice 4 [false; true; true; false] 1 2. *)
(* Compute splice 5 [false; false; false; false; false] 2 3 2 [true; true]. *)
