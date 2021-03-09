Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

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

  Definition to_nat (bits: Bits) : nat :=
    fst (fold_left add_bit_carry bits (0,0)).

  Lemma to_nat_zero: forall w, to_nat (zero w) = 0.
  Admitted.

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

  (* Compute slice 4 [false; true; true; false] 1 2. *)
  (* Compute splice 5 [false; false; false; false; false] 2 3 2 [true; true]. *)
End Bitwise.

