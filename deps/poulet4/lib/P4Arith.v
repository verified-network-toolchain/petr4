Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Lemma exp_ge_one : forall n1 n2 : Z, 0 < n1 -> 0 <= n2 -> 1 <= n1 ^ n2.
Proof.
  intros n1 n2 H.
  rewrite <- Z.pow_0_r with n1.
  apply Z.pow_le_mono_r; lia.
Qed.

(** * Unsigned Integers *)
Module BitArith.
  Import Z.

  Section Operations.
    Variable (width : positive).

    Definition upper_bound : Z := 2 ^ pos width.

    Definition maxZ : Z := upper_bound - 1.

    (** Precondition for operations. *)
    Definition bound (n : Z) : Prop := -1 < n < upper_bound.

    (* Saturating bound *)
    Definition sat_bound (n : Z) : Z :=
      if (n >? maxZ)
      then maxZ
      else if (n <? 0) then 0 else n.
    (**[]*)

    (* Modular bound *)
    Definition mod_bound (n : Z) : Z := n mod upper_bound.

    (* Modular bound with unsigned bit output *)
    Definition bit_bound := mod_bound.

    Lemma upper_bound_ge_1 : 1 <= upper_bound.
    Proof. unfold upper_bound; apply exp_ge_one; lia. Qed.

    Lemma sat_bound_bound : forall n, bound (sat_bound n).
    Proof.
      intros n; unfold sat_bound, bound, maxZ.
      destruct (n >? upper_bound -1) eqn:?H.
      - pose proof upper_bound_ge_1. lia.
      - rewrite gtb_ltb in H. rewrite ltb_ge in H.
        destruct (n <? 0) eqn: ?H.
        + pose proof upper_bound_ge_1. lia.
        + rewrite ltb_ge in H0. lia.
    Qed.

    Lemma mod_bound_bound: forall n: Z, bound (mod_bound n).
    Proof.
      intros. unfold bound, mod_bound. pose proof upper_bound_ge_1.
      pose proof (mod_pos_bound n upper_bound). lia.
    Qed.

    (** Bitwise negation. *)
    Definition neg (n : Z) : Z := mod_bound (opp n).

    (** Saturating Addition *)
    Definition plus_sat (a b : Z) : Z := sat_bound (a + b).

    (** Modular Addition *)
    Definition plus_mod (a b : Z) : Z := mod_bound (a + b).

    (** Saturating Subtraction *)
    Definition minus_sat (a b : Z) : Z := sat_bound (a - b).

    (** Modular Subtraction *)
    Definition minus_mod (a b : Z) : Z := mod_bound (a - b).

    (** Modular Multiplication *)
    Definition mult_mod (a b : Z) : Z := mod_bound (a * b).

    (** Modular Division *)
    Definition div_mod (a b : Z) : Z := mod_bound (a / b).

    (** Modular Modulo *)
    Definition modulo_mod (a b : Z) : Z := mod_bound (a mod b).

    Lemma mod_bound_double_add: forall a b,
        mod_bound (a + mod_bound b) = mod_bound (a + b).
    Proof.
      intros. unfold mod_bound. rewrite add_mod_idemp_r. easy.
      pose proof upper_bound_ge_1. lia.
    Qed.

    Lemma minus_mod_eq: forall a b : Z, minus_mod a b = plus_mod a (neg b).
    Proof.
      intros. unfold minus_mod, plus_mod, neg. rewrite mod_bound_double_add.
      now rewrite add_opp_r.
    Qed.

    Lemma bound_neg: forall n: Z,
        bound n -> neg n = if (n =? 0) then 0 else upper_bound - n.
    Proof.
      unfold bound. intros. unfold neg, mod_bound. destruct (n =? 0) eqn: ?H.
      - rewrite eqb_eq in H0. subst n. vm_compute. easy.
      - rewrite eqb_neq in H0. unfold modulo.
        assert (upper_bound > 0) by (pose proof upper_bound_ge_1; lia).
        pose proof (Z_div_mod (- n) upper_bound H1).
        remember (div_eucl (- n) upper_bound). destruct p as [q r]. destruct H2.
        assert (0 < n < upper_bound) by lia. clear H0 H. rewrite <- add_opp_r.
        rewrite H2. clear Heqp. rewrite add_assoc.
        rewrite <- add_0_l at 1. rewrite add_cancel_r. rewrite Zred_factor2.
        assert (n = upper_bound * (- q) - r) by lia. clear H2. subst n.
        destruct (Z_le_gt_dec 0 q). 1: exfalso; lia.
        destruct (Z_le_gt_dec q (-2)).
        + exfalso. assert (- q >= 2) by lia. destruct H4. remember (- q).
          clear q g l Heqz. apply lt_asymm in H2. apply H2. clear H2.
          apply lt_le_trans with (upper_bound * 2 - r). 1: lia.
          apply sub_le_mono_r. apply Zmult_le_compat_l; lia.
        + assert (q = - 1) by lia. subst q. lia.
    Qed.

    Lemma neg_involutive : forall n : Z, bound n -> neg (neg n) = n.
    Proof.
      intros. pose proof (bound_neg n H). rewrite H0. destruct (n =? 0) eqn:?H.
      - rewrite eqb_eq in H1. subst. vm_compute. easy.
      - rewrite eqb_neq in H1. rewrite bound_neg.
        + assert (upper_bound - n =? 0 = false). {
            rewrite eqb_neq. unfold bound in H. lia.
          } rewrite H2. lia.
        + unfold bound in *; lia.
    Qed.

    Lemma plus_mod_assoc: forall a b c,
        plus_mod (plus_mod a b) c = plus_mod a (plus_mod b c).
    Proof.
      intros. unfold plus_mod. rewrite (add_comm (mod_bound (a + b))).
      rewrite !mod_bound_double_add. rewrite (add_comm c (a + b)).
      now rewrite add_assoc.
    Qed.
    (**[]*)

    (* The following bitwise operation may be wrong *)

    (** Right Shift *)
    Definition shift_right (a b : Z) : Z := mod_bound (shiftr a b).

    (** Left Shift *)
    Definition shift_left (a b : Z) : Z := mod_bound (shiftl a b).

    (** Bitwise operations may not need mod_bound given that the
        arguments are bounded **)

    (** Bitwise Not *)
    Definition bit_not (a : Z) := mod_bound (maxZ - a).

    (** Bitwise And *)
    Definition bit_and (a b : Z) := mod_bound (land a b).

    (** Bitwise Or *)
    Definition bit_or (a b : Z) := mod_bound (lor a b).

    (** Bitwise Xor *)
    Definition bit_xor (a b : Z) := mod_bound (lxor a b).

  End Operations.

  (** Bitwise concatination of bit with bit/int *)
  Definition concat (w1 w2 : positive) (z1 z2 : Z) : Z :=
    mod_bound (w1+w2) (shiftl z1 (pos w2) + (bit_bound w2 z2)).
  (**[]*)

End BitArith.

Ltac unfold_bit_operation :=
  match goal with
  (* | |- context [ BitArith.neg _ ] => unfold BitArith.neg *)
  | |- context [ BitArith.plus_sat _ _ ] => unfold BitArith.plus_sat
  (* | |- context [ BitArith.plus_mod _ _ ] => unfold BitArith.plus_mod *)
  | |- context [ BitArith.minus_mod _ _ ] => unfold BitArith.minus_mod
  | |- context [ BitArith.shift_right _ _ ] => unfold BitArith.shift_right
  | |- context [ BitArith.shift_left _ _ ] => unfold BitArith.shift_left
  | |- context [ BitArith.bit_and _ _ ] => unfold BitArith.bit_and
  | |- context [ BitArith.bit_xor _ _ ] => unfold BitArith.bit_xor
  | |- context [ BitArith.bit_or _ _ ] => unfold BitArith.bit_or
  end.

(** * Signed Integers *)
Module IntArith.
  Import Z.

  Section Operations.
    Variable (width : positive).

    Definition mod_amt : Z := 2 ^ (pos width).

    Definition upper_bound : Z := 2 ^ (pos width - 1).

    Lemma mod_amt_gt_0: mod_amt > 0.
    Proof.
      cut (1 <= mod_amt).
      - intros. lia.
      - unfold mod_amt. apply exp_ge_one; lia.
    Qed.

    Lemma mod_amt_neq_0: mod_amt <> 0. Proof. pose proof mod_amt_gt_0. lia. Qed.

    Lemma mod_amt_2_upper_bound: mod_amt = 2 * upper_bound.
    Proof.
      unfold mod_amt, upper_bound. rewrite <- pow_succ_r. 2: lia.
      rewrite Zminus_succ_l. f_equal. lia.
    Qed.

    Lemma upper_bound_ge_1 : 1 <= upper_bound.
    Proof. unfold upper_bound; apply exp_ge_one; lia. Qed.

    Definition maxZ : Z := upper_bound - 1.

    Definition minZ : Z := - upper_bound.

    (** Precondition for operations *)
    Definition bound (z : Z) : Prop := (minZ <= z <= maxZ)%Z.

    (* Saturating bound *)
    Definition sat_bound (z : Z) :=
      if (z >? maxZ)%Z then maxZ
      else if (z <? minZ)%Z then minZ else z.

    (* Modular bound with unsigned bit output *)
    Definition bit_bound (n : Z) : Z := n mod mod_amt.

    (* Modular bound *)
    Definition mod_bound (n : Z) : Z :=
      let m := bit_bound n in
      if (m <? upper_bound) then m else m - mod_amt.
    (**[]*)

    Lemma sat_bound_bound : forall z, bound (sat_bound z).
    Proof.
      intros z; unfold sat_bound, bound, minZ, maxZ.
      destruct (z >? upper_bound - 1)%Z eqn:eqnz.
      - clear z eqnz; split; try lia.
        pose proof upper_bound_ge_1; lia.
      - rewrite gtb_ltb in eqnz.
        apply ltb_ge in eqnz.
        destruct (z <? - upper_bound)%Z eqn:eqnz'.
        + clear z eqnz eqnz' z; try lia.
          pose proof upper_bound_ge_1; lia.
        + apply ltb_ge in eqnz'. lia.
    Qed.

    Lemma mod_bound_bound: forall z, bound (mod_bound z).
    Proof.
      intros. unfold mod_bound, bit_bound, bound, minZ, maxZ.
      pose proof (Z_mod_lt z mod_amt mod_amt_gt_0).
      remember (z mod mod_amt) as zz. clear z Heqzz. rename zz into z.
      pose proof upper_bound_ge_1. destruct (z <? upper_bound) eqn: ?H.
      - rewrite ltb_lt in H1. lia.
      - rewrite ltb_ge in H1. pose proof mod_amt_2_upper_bound. lia.
    Qed.

    (** Negation. *)
    Definition neg (z : Z) : Z := mod_bound (opp z).

    (** Saturating Addition *)
    Definition plus_sat (a b : Z) : Z := sat_bound (a + b).

    (** Saturating Subtraction *)
    Definition minus_sat (a b : Z) : Z := sat_bound (a - b).

    (** Modular Addition *)
    Definition plus_mod (a b : Z) : Z := mod_bound (a + b).

    (** Modular Subtraction *)
    Definition minus_mod (a b : Z) : Z := mod_bound (a - b).

    (** Modular Multiplication *)
    Definition mult_mod (a b : Z) : Z := mod_bound (a * b).

    Lemma bound_eq: forall z, bound z -> mod_bound z = z.
    Proof.
      unfold bound, minZ, maxZ. intros. unfold mod_bound, bit_bound. pose proof mod_amt_neq_0.
      destruct (Z_le_gt_dec 0 z).
      - pose proof mod_amt_2_upper_bound.
        assert (z mod mod_amt <? upper_bound = true). {
          rewrite ltb_lt. rewrite mod_small; lia. }
        rewrite H2. rewrite mod_small; lia.
      - destruct H. clear H1. pose proof mod_amt_2_upper_bound.
        assert (z mod mod_amt <? upper_bound = false). {
          rewrite ltb_ge. unfold modulo. remember (div_eucl z mod_amt).
          destruct p as [q r]. pose proof (Z_div_mod z mod_amt mod_amt_gt_0).
          rewrite <- Heqp in H2. destruct H2. clear Heqp. destruct (Z_le_gt_dec 0 q).
          - exfalso. lia.
          - assert (r = z - mod_amt * q) by lia. clear H2. subst r.
            rewrite H1. clear H3. transitivity (- upper_bound - 2 * upper_bound * q).
            2: lia. apply Zplus_le_reg_l with (p := upper_bound).
            rewrite add_sub_assoc. rewrite add_opp_r. rewrite sub_diag.
            rewrite sub_0_l. rewrite add_diag. rewrite !Zopp_mult_distr_r.
            rewrite <- mul_1_r at 1. apply Zmult_le_compat_l; lia. }
        rewrite H2. rewrite ltb_ge in H2. unfold modulo in *.
        remember (div_eucl z mod_amt). destruct p as [q r].
        pose proof (Z_div_mod z mod_amt mod_amt_gt_0). rewrite <- Heqp in H3.
        destruct H3. subst z. destruct (Z_le_gt_dec 0 q). 1: exfalso; lia.
        destruct (Z_le_gt_dec q (-2)).
        + exfalso. apply Zle_not_gt in H. apply H. clear H. rewrite H1.
          rewrite H1 in H4. clear Heqp H0 g H1 g0.
          apply Zgt_trans with (2 * upper_bound * q + 2 * upper_bound). 2: lia.
          pose proof upper_bound_ge_1. clear r H2 H4. apply lt_gt.
          apply le_lt_trans with (2 * upper_bound * (-2) + 2 * upper_bound). 2: lia.
          apply Zplus_le_compat_r. apply mul_le_mono_nonneg_l. lia. easy.
        + assert (q = -1) by lia. subst q. lia.
    Qed.

    Lemma neg_bound: forall n: Z, bound n -> n <> minZ -> bound (- n).
    Proof. unfold bound. unfold minZ. unfold maxZ. intros. lia. Qed.

    Lemma neg_involutive : forall n : Z, bound n -> neg (neg n) = n.
    Proof.
      intros. pose proof upper_bound_ge_1. pose proof mod_amt_2_upper_bound.
      unfold neg. destruct (eq_dec n minZ).
      - subst. unfold mod_bound, bit_bound, minZ. rewrite opp_involutive.
        assert (upper_bound mod mod_amt = upper_bound). { rewrite mod_small; lia. }
        assert (upper_bound mod mod_amt <? upper_bound = false). {
          rewrite ltb_ge. rewrite H2. easy. } rewrite H3. rewrite H2.
        assert (upper_bound - mod_amt = - upper_bound) by lia. rewrite H4.
        rewrite opp_involutive. rewrite H3. rewrite H2. now rewrite H4.
      - assert (bound (- n)) by now apply neg_bound.
        rewrite (bound_eq (- n)); auto. rewrite opp_involutive. now rewrite bound_eq.
    Qed.

    Lemma mod_bound_double_add: forall a b,
        mod_bound (a + mod_bound b) = mod_bound (a + b).
    Proof.
      pose proof mod_amt_neq_0.
      intros. unfold mod_bound, bit_bound. destruct (b mod mod_amt <? upper_bound) eqn:?H.
      - rewrite add_mod_idemp_r; easy.
      - assert ((a + (b mod mod_amt - mod_amt)) mod mod_amt = (a + b) mod mod_amt). {
          rewrite add_mod; auto. rewrite Zminus_mod_idemp_l.
          rewrite <- add_mod; auto. rewrite add_sub_assoc.
          rewrite Zminus_mod. rewrite Z_mod_same_full. rewrite sub_0_r.
          rewrite mod_mod; auto. } rewrite H1. easy.
    Qed.

    Lemma plus_mod_neg: forall a b, plus_mod a (-b) = plus_mod a (neg b).
    Proof. intros. unfold plus_mod, neg. rewrite mod_bound_double_add. easy. Qed.

    Lemma minus_mod_eq: forall a b : Z, minus_mod a b = plus_mod a (neg b).
    Proof.
      intros. rewrite <- plus_mod_neg. unfold minus_mod, plus_mod.
      rewrite add_opp_r. easy.
    Qed.

    Lemma plus_mod_assoc: forall a b c,
        plus_mod (plus_mod a b) c = plus_mod a (plus_mod b c).
    Proof.
      intros. unfold plus_mod. rewrite (add_comm (mod_bound (a + b))).
      rewrite !mod_bound_double_add. rewrite (add_comm c (a + b)).
      now rewrite add_assoc.
    Qed.

    (* The following bitwise operation may be wrong *)

    (** Arithmetic shift left *)
    Definition shift_left (a b : Z) : Z := mod_bound (shiftl a b).

    (** Arithmetic shift right *)
    Definition shift_right (a b : Z) : Z := mod_bound (shiftr a b).

    (** Bitwise operations may not need mod_bound given that the
        arguments are bounded **)

    (** Bitwise Not *)
    Definition bit_not (a : Z) := mod_bound ( - (a + 1)).

    (** Bitwise And *)
    Definition bit_and (a b : Z) : Z := mod_bound (land a b).

    (** Bitwise Or *)
    Definition bit_or (a b : Z) : Z := mod_bound (lor a b).

    (** Bitwise Xor *)
    Definition bit_xor (a b : Z) : Z := mod_bound (lxor a b).

  End Operations.

  (** Bitwise concatination of int with int/bit *)
  Definition concat (w1 w2 : positive) (z1 z2 : Z) : Z :=
    mod_bound (w1+w2) (shiftl z1 (pos w2) + (bit_bound w2 z2)).
  (**[]*)

End IntArith.

(*
Compute (IntArith.concat 4 4 (-16) 31).
Compute (IntArith.concat 4 4 15 31).
Compute (IntArith.concat 4 4 (-8) 32).
Compute (IntArith.concat 4 4 (-2) (-1)).
Compute (BitArith.concat 4 4 (-16) 31).
Compute (BitArith.concat 4 4 15 31).
Compute (BitArith.concat 4 4 (-8) 32).
Compute (BitArith.concat 4 4 (-2) (-1)).

Compute (IntArith.bit_not 4 9).
Compute (IntArith.bit_not 4 (-1)).
Compute (IntArith.bit_not 4 (-8)).
Compute (IntArith.bit_not 4 7).

Compute (BitArith.mult_mod 4 3 5).
Compute (IntArith.mult_mod 4 2 4).
Compute (IntArith.shift_left 4 6 1).
Compute (IntArith.shift_right 4 (-4) 10).
Compute (IntArith.shift_right 4 4 3).
Compute (IntArith.shift_left 4 (-4) 2).

Compute (IntArith.neg 32 (- 2147483648)).

Compute (IntArith.plus_mod 32 (-500) (-200)).

Compute (IntArith.minus_mod 32 20 1000). *)


Ltac unfold_int_operation :=
  match goal with
  | |- context [ IntArith.neg _ ] => unfold IntArith.neg
  | |- context [ IntArith.plus_sat _ _ ] => unfold IntArith.plus_sat
  | |- context [ IntArith.minus_sat _ _ ] => unfold IntArith.minus_sat
  | |- context [ IntArith.plus_mod _ _ ] => unfold IntArith.plus_mod
  | |- context [ IntArith.minus_mod _ _ ] => unfold IntArith.minus_mod
  | |- context [ IntArith.shift_right _ _ ] => unfold IntArith.shift_right
  | |- context [ IntArith.shift_left _ _ ] => unfold IntArith.shift_left
  | |- context [ IntArith.bit_and _ _ ] => unfold IntArith.bit_and
  | |- context [ IntArith.bit_xor _ _ ] => unfold IntArith.bit_xor
  | |- context [ IntArith.bit_or _ _ ] => unfold IntArith.bit_or
  end.
