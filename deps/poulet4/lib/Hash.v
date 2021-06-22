Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Hexadecimal.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import Poulet4.Bitwise.

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
  Variable (poly : uint). 
  Variable (init : uint).
  Variable (xor_out : uint).
  Variable (refin : bool).
  Variable (refout : bool).

  (* Input *)
  Variable (in_width : nat).
  Variable (input : Z).

  Definition poly_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N (N.of_hex_uint poly) out_width).

  Definition init_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N (N.of_hex_uint init) out_width).

  Definition xor_out_bits : Bits :=
    Bitwise.little_to_big (Bitwise.of_N (N.of_hex_uint xor_out) out_width).

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
      Bitwise.zero (in_width_round - in_width)
      ++ (Bitwise.of_N (Z.to_N input) in_width) in
    let input_rev :=
      if refin 
      then concat (map (@rev bool) (group_list input_round 8))
      else input_round in
    let input_padded := (Bitwise.zero out_width) ++ input_rev in
      Bitwise.xor init_bits (Bitwise.little_to_big input_padded).

  Definition compute_crc : Z :=
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
    Z.of_N (Bitwise.to_N 
      (Bitwise.big_to_little (Bitwise.xor xor_out_bits crc_rev))).

End CRC.

(* Compute (compute_crc 16 (D8 (D0 (D0 (D5 Nil)))) (D0 Nil) (D0 Nil)
         true true 12 3911). *)
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
