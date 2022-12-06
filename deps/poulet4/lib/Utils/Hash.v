Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import Poulet4.P4light.Semantics.Bitwise.

(* CRC Steps:
    1. BMV2-specific: the [input] is appended with zeros to the end
      to expand its length to a multiple of 8 bits.
    2. If [refin], the bits in each byte of the input are reversed.
    3. The input is appended with [out_width] number of zeros to the end.
    4. The first [out_width] bits of the input is XOR'ed with [init].
    5. The regular CRC algorithm is run on the input with the polynomail [poly].
    6. If [refout], all bits in the remainder are reversed.
    7. The remainder is XOR'ed with [xor_out].
*)

Section CRC.
  (* CRC algorithm configurations *)
  Variable (out_width : nat).
  Variable (poly : N).
  Variable (init : N).
  Variable (xor_out : N).
  Variable (refin : bool).
  Variable (refout : bool).

  (* Input *)
  Variable (input : Bits).

  Definition in_width : nat := List.length input.

  Definition poly_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N poly out_width).

  Definition init_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N init out_width).

  Definition xor_out_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N xor_out out_width).

  Definition in_width_round : nat := (in_width + 7) / 8 * 8.

  Definition group_list {A : Type} (l : list A) (n : nat) : list (list A) :=
    let group_list' (i : A) (acc_n_m : list (list A) * (nat * nat)) :=
      let (acc, n_m) := acc_n_m in
      let (n, m) := n_m in
      match m, acc with
      | O, _  => ([i] :: acc, (n, n))
      | S m', hd :: tl => ((i :: hd) :: tl, (n, m'))
      (* never hit *)
      | _, _ => (acc, (n, m))
      end
    in fst (fold_right group_list' ([], (n-1, O)) l).

  Definition input_bits : Bits :=
    let input_round :=
      Bitwise.zero (in_width_round - in_width) ++ input in
    let input_rev :=
      if refin
      then concat (map (@rev bool) (group_list input_round 8))
      else input_round in
    let input_padded := (Bitwise.zero out_width) ++ input_rev in
      Bitwise.xor init_bits (Bitwise.little_to_big input_padded).

  Definition compute_crc : Bits :=
    let fix compute_crc' (bits : Bits) (i : nat) :=
      if i <=? out_width then bits
      else
        match i with
        | S i' =>
          match bits with
          | false :: bits' => compute_crc' bits' i'
          | true :: bits' => compute_crc' (Bitwise.xor poly_bits bits') i'
          (* never hit *)
          | [] => []
          end
        (* never hit *)
        | O => []
        end in
    let crc_output := compute_crc' input_bits (length input_bits) in
    let crc_rev := if refout then rev crc_output else crc_output in
    Bitwise.big_to_little (Bitwise.xor xor_out_bits crc_rev).

  Lemma length_xor_out_bits: length xor_out_bits = out_width.
  Proof.
    unfold xor_out_bits. unfold little_to_big. now rewrite rev_length, of_N_length.
  Qed.

  Lemma length_poly_bits: length poly_bits = out_width.
  Proof.
    unfold poly_bits. unfold little_to_big. now rewrite rev_length, of_N_length.
  Qed.

  Lemma length_compute_crc: length compute_crc = out_width.
  Proof.
    unfold compute_crc.
    remember (fix compute_crc' (bits : Bits) (i : nat) {struct i} : Bits :=
                if i <=? out_width
                then bits
                else
                  match i with
                  | 0 => []
                  | S i' =>
                      match bits with
                      | [] => []
                      | true :: bits' => compute_crc' (xor poly_bits bits') i'
                      | false :: bits' => compute_crc' bits' i'
                      end
                  end) as compute_crc'. rename Heqcompute_crc' into Hcrc'.
    unfold big_to_little. rewrite rev_length. unfold xor. rewrite map2_length.
    cut (max (length xor_out_bits)
             (length (compute_crc' input_bits (length input_bits))) = out_width).
    - intros. destruct refout; auto. rewrite rev_length; auto.
    - rewrite length_xor_out_bits.
      assert (forall bits i, i = length bits ->
                        length (compute_crc' bits i) =
                          if (i <=? out_width) then (length bits) else out_width). {
        intros. revert bits H. induction i; intros.
        - rewrite Hcrc'. simpl. auto.
        - rewrite Hcrc', <- Hcrc'. destruct (S i <=? out_width) eqn:?H; auto.
          destruct bits.
          + simpl in H. inversion H.
          + simpl in H. apply Nat.succ_inj in H. rewrite Nat.leb_gt in H0.
            rewrite Nat.lt_succ_r in H0. apply Nat.lt_eq_cases in H0. destruct H0.
            * rewrite <- Nat.leb_gt in H0.
              destruct b; rewrite IHi; auto; try (now rewrite H0).
              unfold xor. rewrite map2_length. rewrite length_poly_bits.
              rewrite Nat.leb_gt in H0. subst i.
              rewrite Nat.max_r; auto. apply Nat.lt_le_incl; auto.
            * assert (length (xor poly_bits bits) = i). {
                unfold xor. rewrite map2_length, <- H, length_poly_bits, H0.
                apply Nat.max_id. }
              destruct b; rewrite IHi; auto; rewrite H0, Nat.leb_refl; auto. }
      rewrite H; auto. destruct (length input_bits <=? out_width) eqn:?H.
      + rewrite Nat.leb_le in H0. rewrite Nat.max_l; auto.
      + apply Nat.max_id.
  Qed.

End CRC.

Module CRC_Test.

  Local Open Scope hex_N_scope.

  Goal Bitwise.to_N (compute_crc 16 0x8005 0x0 0x0 true true
                       (Bitwise.of_N 0x12345678 32)) = 0x347B.
  Proof. reflexivity. Qed.

  Goal Bitwise.to_N (compute_crc 32 0x04C11DB7 0xFFFFFFFF 0xFFFFFFFF true true
                       (Bitwise.of_N 0x12345678 32)) = 0x4A090E98.
  Proof. reflexivity. Qed.

End CRC_Test.

(* Z.of_N (Bitwise.to_N Bits *)
(* Example:
    last 15 bits of 0x0501 is 1281, rounded into 0x0A02 => output 24967 = 0x6187
    first 12 bits of 0xF470 is 3911, rounded into 0xF470 => output 9287 = 0x2447 *)
(* Compute (compute_crc 32 (D0 (D4 (Dc (D1 (D1 (Dd (Db (D7 Nil))))))))
         (Df (Df (Df (Df (Df (Df (Df (Df Nil))))))))
         (Df (Df (Df (Df (Df (Df (Df (Df Nil))))))))
         true	true 12 3911). *)
(* Ref:
    http://ross.net/crc/download/crc_v3.txt
    https://stackoverflow.com/questions/5047494/python-crc-32-woes
    https://crccalc.com/ *)
