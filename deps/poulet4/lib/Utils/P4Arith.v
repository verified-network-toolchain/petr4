Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Require Import VST.zlist.Zlist.
Require Import Coq.Lists.List.
Require Import Poulet4.P4light.Syntax.SyntaxUtil.
Import ListNotations.

Open Scope Z_scope.

Lemma nat_to_Z_to_N : forall n,
    Z.to_N (Z.of_nat n) = N.of_nat n.
Proof. lia. Qed.

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
    Variable (width : N).

    Definition upper_bound : Z := 2 ^ (Z.of_N width).

    Definition maxZ : Z := upper_bound - 1.

    (** Precondition for operations. *)
    Definition bound (n : Z) : Prop := -1 < n < upper_bound.

    Definition boundb (n : Z) : bool :=
      (-1 <? n) && (n <? upper_bound).

    Lemma bound_boundb : forall n,
        bound n -> boundb n = true.
    Proof.
      unfold bound, boundb; lia.
    Qed.

    Lemma boundb_bound : forall n,
        boundb n = true -> bound n.
    Proof.
      unfold bound,boundb; lia.
    Qed.

    Lemma bound_iff : forall n,
        bound n <-> boundb n = true.
    Proof.
      Local Hint Resolve boundb_bound : core.
      Local Hint Resolve bound_boundb : core.
      intuition.
    Qed.

    Lemma bound_reflect : forall n,
        reflect (bound n) (boundb n).
    Proof.
      intro n.
      Local Hint Constructors reflect : core.
      Local Hint Resolve bound_iff : core.
      destruct (boundb n) eqn:Heq; auto.
      constructor. intros H.
      apply bound_boundb in H.
      rewrite H in Heq. discriminate.
    Qed.

    Lemma bound0 : bound 0.
    Proof.
      unfold bound, upper_bound.
      pose proof exp_ge_one 2 (Z.of_N width). lia.
    Qed.

    (* Modular bound *)
    Definition mod_bound (n : Z) : Z := n mod upper_bound.

    (* Saturating bound *)
    Definition sat_bound (n : Z) : Z :=
      if (n >? maxZ)
      then maxZ
      else if (n <? 0) then 0 else n.
    (**[]*)

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

    Lemma neg_mod_bound: forall n, neg (mod_bound n) = neg n.
    Proof.
      intros. unfold neg. unfold mod_bound. pose proof upper_bound_ge_1.
      destruct (Z.eq_dec (n mod upper_bound) 0).
      - rewrite e. apply Z_mod_zero_opp in e. 2: lia. rewrite e.
        simpl. apply Zmod_0_l.
      - rewrite (mod_opp_l_nz n) by lia.
        rewrite mod_opp_l_nz; try lia; rewrite Zmod_mod; auto.
    Qed.

    Lemma plus_mod_assoc: forall a b c,
        plus_mod (plus_mod a b) c = plus_mod a (plus_mod b c).
    Proof.
      intros. unfold plus_mod. rewrite (add_comm (mod_bound (a + b))).
      rewrite !mod_bound_double_add. rewrite (add_comm c (a + b)).
      now rewrite add_assoc.
    Qed.

    Lemma plus_mod_mod: forall a b,
        plus_mod (mod_bound a) (mod_bound b) = plus_mod a b.
    Proof.
      intros. unfold plus_mod. rewrite mod_bound_double_add.
      rewrite (Z.add_comm (mod_bound a)). rewrite mod_bound_double_add.
      now rewrite Z.add_comm.
    Qed.

    Lemma minus_mod_mod: forall a b,
        minus_mod (mod_bound a) (mod_bound b) = minus_mod a b.
    Proof.
      intros. rewrite !minus_mod_eq. unfold plus_mod.
      rewrite Z.add_comm. rewrite mod_bound_double_add. rewrite neg_mod_bound.
      now rewrite Z.add_comm.
    Qed.

    Lemma mult_mod_mod: forall a b,
        mult_mod (mod_bound a) (mod_bound b) = mult_mod a b.
    Proof.
      intros. unfold mult_mod. unfold mod_bound. pose proof upper_bound_ge_1.
      rewrite <- mul_mod; lia.
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

  (** NOTE: this code was taken from [Semantics.v].
      Ref:When accessing the bits of negative numbers, all functions below will
      use the two's complement representation.
      For instance, -1 will correspond to an infinite stream of true bits.
      https://coq.inria.fr/library/Coq.ZArith.BinIntDef.html *)
  Definition bitstring_slice (i : Z) (lo hi : positive) : Z :=
    let mask := (Z.pow 2 (Zpos (hi - lo + 1)) - 1)%Z in
    Z.land (Z.shiftr i (Zpos lo)) mask.

  (** Bitwise concatination of bit with bit/int *)
  Definition concat (w1 w2 : N) (z1 z2 : Z) : Z :=
    mod_bound (w1 + w2) (shiftl z1 (Z.of_N w2) + (mod_bound w2 z2)).

  Fixpoint lbool_to_val (bits: list bool) (order: Z) (res : Z) : Z :=
    match bits with
    | [] => res
    | false :: tl => lbool_to_val tl (Z.shiftl order 1) res
    | true :: tl => lbool_to_val tl (Z.shiftl order 1) (res + order)
    end.

  Lemma lbool_to_val_app: forall l1 l2 o r,
      lbool_to_val (l1 ++ l2) o r =
        lbool_to_val l2 (Z.shiftl o (Zlength l1)) (lbool_to_val l1 o r).
  Proof.
    induction l1; intros.
    - simpl. easy.
    - rewrite <- app_comm_cons. cbn [lbool_to_val].
      destruct a; rewrite IHl1; f_equal; rewrite shiftl_shiftl by lia;
        f_equal; rewrite Zlength_cons; lia.
  Qed.

  Lemma lbool_to_val_1_0: forall l o r,
      lbool_to_val l o r = (lbool_to_val l 1 0) * o + r.
  Proof.
    induction l; intros; cbn [lbool_to_val]. 1: now simpl. destruct a.
    - simpl shiftl at 2. rewrite add_0_l.
      rewrite IHl. rewrite (IHl 2 1). rewrite shiftl_mul_pow2 by lia. lia.
    - simpl shiftl at 2. rewrite IHl. rewrite (IHl 2 0).
      rewrite shiftl_mul_pow2 by lia. lia.
  Qed.

  (* Convert from little-endian (list bool) to (width:nat, value:Z) *)
  Definition le_from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val bits 1 0).
  (**[]*)

  (* Convert from big-endian (list bool) to (width:nat, value:Z) *)
  Definition from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val (rev bits) 1 0).
  (**[]*)


  Lemma lbool_to_val_lower : forall bits order res,
      0 <= order ->
      0 <= res ->
      0 <= lbool_to_val bits order res.
  Proof.
    intro bits; induction bits as [| [|] bits IHbits];
      intros order res Horder Hres;
      unfold lbool_to_val; fold lbool_to_val; try lia; auto.
    - apply IHbits; try lia.
      rewrite shiftl_mul_pow2 by lia; lia.
    - apply IHbits; try lia.
      rewrite shiftl_mul_pow2 by lia; lia.
  Qed.
  
  Lemma le_from_lbool_bound : forall bits,
      uncurry bound (le_from_lbool bits).
  Proof.
    intro bits; cbn. unfold bound; split.
    - pose proof lbool_to_val_lower bits 1 0 as H; lia.
    - unfold upper_bound.
      rewrite Z2N.id by apply Zlength_nonneg.
      (* TODO: idk what lemma to prove... *)
  Admitted.

  Lemma from_lbool_bound : forall bits,
      uncurry bound (from_lbool bits).
  Proof.
    unfold from_lbool.
    intros.
    rewrite <- Zlength_rev.
    apply le_from_lbool_bound.
  Qed.
  
End BitArith.

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

    Lemma bound0 : bound 0.
    Proof.
      unfold bound, minZ, maxZ, upper_bound.
      pose proof exp_ge_one 2 (pos width - 1). lia.
    Qed.

    (* Modular bound *)
    Definition mod_bound (n : Z) : Z :=
      let m := n mod mod_amt in
      if (m <? upper_bound) then m else m - mod_amt.

    (* Saturating bound *)
    Definition sat_bound (z : Z) :=
      if (z >? maxZ)%Z then maxZ
      else if (z <? minZ)%Z then minZ else z.
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
      intros. unfold mod_bound, bound, minZ, maxZ.
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
      unfold bound, minZ, maxZ. intros. unfold mod_bound. pose proof mod_amt_neq_0.
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
      - subst. unfold mod_bound, minZ. rewrite opp_involutive.
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
      intros. unfold mod_bound. destruct (b mod mod_amt <? upper_bound) eqn:?H.
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

    Lemma plus_mod_mod: forall a b,
        plus_mod (mod_bound a) (mod_bound b) = plus_mod a b.
    Proof.
      intros. unfold plus_mod. rewrite mod_bound_double_add.
      rewrite (Z.add_comm (mod_bound a)). rewrite mod_bound_double_add.
      now rewrite Z.add_comm.
    Qed.

    Lemma mult_mod_mod: forall a b,
        mult_mod (mod_bound a) (mod_bound b) = mult_mod a b.
    Proof.
      intros. unfold mult_mod. unfold mod_bound. pose proof mod_amt_neq_0.
      assert (forall x y, (x * (y - mod_amt)) mod mod_amt = (x * y) mod mod_amt). {
        intros. rewrite mul_sub_distr_l. rewrite Zminus_mod.
        rewrite mod_mul; auto. rewrite sub_0_r. now rewrite mod_mod. }
      destruct (a mod mod_amt <? upper_bound), (b mod mod_amt <? upper_bound).
      - rewrite <- mul_mod; auto.
      - rewrite H0. rewrite <- mul_mod; auto.
      - rewrite Z.mul_comm, H0, Z.mul_comm, <- mul_mod; auto.
      - rewrite H0, Z.mul_comm, H0, Z.mul_comm, <- mul_mod; auto.
    Qed.

    Lemma neg_mod_bound: forall n, neg (mod_bound n) = neg n.
    Proof.
      intros. unfold neg. unfold mod_bound. pose proof mod_amt_neq_0.
      destruct (Z.eq_dec (n mod mod_amt) 0).
      - rewrite e. assert (0 <? upper_bound = true). {
          rewrite ltb_lt. pose proof upper_bound_ge_1. lia. }
        pose proof (Z_mod_zero_opp_full _ _ e).
        rewrite H1, H0. rewrite (Z_mod_zero_opp_full _ _ (Zmod_0_l mod_amt)).
        now rewrite H0.
      - assert ((n mod mod_amt) mod mod_amt <> 0). {
          rewrite mod_mod; auto. }
        destruct (n mod mod_amt <? upper_bound).
        + rewrite !Z_mod_nz_opp_full; auto. rewrite mod_mod; auto.
        + assert (forall x, (x + mod_amt) mod mod_amt = x mod mod_amt). {
            intros. rewrite <- (Z_mod_plus_full x 1 mod_amt). now rewrite mul_1_l. }
          rewrite opp_sub_distr, H1. rewrite !Z_mod_nz_opp_full; auto.
          rewrite mod_mod; auto.
    Qed.

    Lemma minus_mod_mod: forall a b,
        minus_mod (mod_bound a) (mod_bound b) = minus_mod a b.
    Proof.
      intros. rewrite !minus_mod_eq. unfold plus_mod.
      rewrite Z.add_comm. rewrite mod_bound_double_add. rewrite neg_mod_bound.
      now rewrite Z.add_comm.
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
  Definition concat (w1 w2 : N) (z1 z2 : Z) : Z :=
    mod_bound (pos_of_N (w1 + w2)) (shiftl z1 (Z.of_N w2) + (BitArith.mod_bound w2 z2)).

  Fixpoint lbool_to_val (bits: list bool) (order: Z) (res: Z): Z :=
    match bits with
    | []
    | [false] => res
    | [true] => res - order
    | false :: tl => lbool_to_val tl (Z.shiftl order 1) res
    | true :: tl => lbool_to_val tl (Z.shiftl order 1) (res + order)
    end.

  Lemma lbool_to_val_cons: forall a l o r,
      l <> nil ->
      lbool_to_val (a :: l) o r =
        lbool_to_val l (Z.shiftl o 1) (r + if a then o else 0).
  Proof.
    intros. cbn [lbool_to_val]. destruct a.
    - destruct l; auto. exfalso; now apply H.
    - destruct l. 1: exfalso; now apply H. now rewrite Z.add_0_r.
  Qed.

  Lemma lbool_to_val_1_0: forall l o r,
      lbool_to_val l o r = lbool_to_val l 1 0 * o + r.
  Proof.
    induction l; intros. 1: now simpl.
    cbn [lbool_to_val]. destruct a, l; try lia;
      replace (shiftl o 1) with (2 * o) by now unfold shiftl.
    - rewrite (IHl (2 * o) _ ). rewrite Z.add_0_l, shiftl_1_l, pow_1_r.
      rewrite (IHl 2 1). lia.
    - rewrite (IHl (2 * o) _ ). rewrite shiftl_1_l, pow_1_r.
      rewrite (IHl 2 0). lia.
  Qed.

  (* Convert from little-endian (list bool) to (width:nat, value:Z) *)
  Definition le_from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val bits 1 0).
  (**[]*)

  (* Convert from big-endian (list bool) to (width:nat, value:Z) *)
  Definition from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val (rev bits) 1 0).
  (**[]*)

End IntArith.

(* Convert from (width:N) and (value:Z) to big-endian (list bool) *)
Fixpoint le_to_lbool' (width: nat) (value: Z) (res: list bool) :=
  match width with
  | S n => le_to_lbool' n (value / 2) ((Z.odd value) :: res)
  | O => res
  end.

Lemma nil_le_to_lbool': forall w v r, le_to_lbool' w v r = le_to_lbool' w v [] ++ r.
Proof.
  induction w; intros; simpl; auto.
  rewrite IHw. rewrite (IHw _ [Z.odd v]).
  rewrite <- app_assoc. simpl. easy.
Qed.

(* Convert from (width:N) and (value:Z) to little-endian (list bool) *)
Definition le_to_lbool (width: N) (value: Z) : list bool :=
  List.rev (le_to_lbool' (N.to_nat width) value []).

Definition to_lbool (width: N) (value: Z) : list bool :=
  le_to_lbool' (N.to_nat width) value [].

Definition to_loptbool (width: N) (value: Z) : list (option bool) :=
  map Some (to_lbool width value).

Lemma length_to_lbool': forall w v r, length (le_to_lbool' w v r) = (w + length r)%nat.
Proof.
  induction w; intros; simpl; auto. simpl.
  rewrite IHw. simpl. lia.
Qed.

Lemma Zlength_to_lbool': forall w v r,
    Zlength (le_to_lbool' w v r) = Z.of_nat w + Zlength r.
Proof. intros. rewrite !Zlength_correct. rewrite length_to_lbool'. lia. Qed.

Lemma Zlength_le_to_lbool: forall w v,
    Zlength (le_to_lbool w v) = Z.of_N w.
Proof.
  intros. unfold le_to_lbool. rewrite Zlength_rev.
  rewrite Zlength_to_lbool'. rewrite Zlength_nil. lia.
Qed.

Lemma Zlength_to_lbool: forall w v,
    Zlength (to_lbool w v) = Z.of_N w.
Proof.
  intros. unfold to_lbool.
  rewrite Zlength_to_lbool'. rewrite Zlength_nil. lia.
Qed.

Lemma length_le_to_lbool : forall w z,
    length (le_to_lbool w z) = N.to_nat w.
Proof.
  intros w z.
  replace (length (le_to_lbool w z))
    with (Z.to_nat (Z.of_nat (length (le_to_lbool w z)))) by lia.
  rewrite <- Zcomplements.Zlength_correct.
  rewrite Zlength_le_to_lbool. lia.
Qed.

Lemma length_to_lbool : forall w z,
    length (to_lbool w z) = N.to_nat w.
Proof.
  intros w z.
  replace (length (to_lbool w z))
    with (Z.to_nat (Z.of_nat (length (to_lbool w z)))) by lia.
  rewrite <- Zcomplements.Zlength_correct.
  rewrite Zlength_to_lbool. lia.
Qed.

Lemma bit_mod_bound_0: forall v, BitArith.mod_bound 0 v = 0.
Proof.
  intros. unfold BitArith.mod_bound, BitArith.upper_bound. simpl. apply Z.mod_1_r.
Qed.

Lemma div_2_mod_2_pow:
  forall v z : Z,
    0 <= z -> (v / 2) mod 2 ^ z * 2 + (if Z.odd v then 1 else 0) = v mod (2 * 2 ^ z).
Proof.
  intros v z H. rewrite (Z_div_mod_eq v 2) at 3 by lia. rewrite Zmod_odd.
  assert (0 < 2 ^ z) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.add_mod by lia. rewrite Z.mul_mod_distr_l by lia.
  destruct (Z.odd v).
  - rewrite Z.mod_1_l by lia. rewrite (Z.mod_small _ (2 * 2 ^ z)). 1: lia.
    assert (0 <= (v / 2) mod 2 ^ z < 2 ^ z) by (apply Z_mod_lt; lia). split; lia.
  - rewrite Zmod_0_l, !Z.add_0_r. rewrite Z.mul_mod_distr_l by lia.
    rewrite <- (Z.add_0_r ((v / 2) mod 2 ^ z)) at 2.
    rewrite Zplus_mod_idemp_l. rewrite Z.add_0_r. lia.
Qed.

Lemma bit_from_to_bool: forall w v,
    BitArith.le_from_lbool (le_to_lbool w v) = (w, BitArith.mod_bound w v).
Proof.
  intros. unfold BitArith.le_from_lbool. rewrite Zlength_le_to_lbool. f_equal. 1: lia.
  unfold le_to_lbool. remember (N.to_nat w). pose proof (Nnat.N2Nat.id w).
  rewrite <- Heqn in H. subst w. clear Heqn. revert v. induction n; intros.
  - simpl. rewrite bit_mod_bound_0. easy.
  - simpl le_to_lbool'. rewrite nil_le_to_lbool'. rewrite rev_app_distr.
    rewrite BitArith.lbool_to_val_app. simpl Z.shiftl. simpl BitArith.lbool_to_val.
    rewrite BitArith.lbool_to_val_1_0. rewrite IHn. unfold BitArith.mod_bound.
    unfold BitArith.upper_bound. rewrite !nat_N_Z. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia. remember (Z.of_nat n).
    assert (0 <= z) by lia. now apply div_2_mod_2_pow.
Qed.

Lemma Z_odd_pow_2_S:
  forall (n : nat) (v : Z), Z.odd (v mod 2 ^ Z.of_nat (S n)) = Z.odd v.
Proof.
  intros n v. rewrite !Zodd_mod. f_equal. rewrite <- Znumtheory.Zmod_div_mod; try lia.
  - exists (2 ^ Z.of_nat n). rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r; lia.
Qed.

Lemma le_to_lbool_bit_mod: forall w v,
    le_to_lbool w (BitArith.mod_bound w v) = le_to_lbool w v.
Proof.
  intros. unfold le_to_lbool. unfold BitArith.mod_bound, BitArith.upper_bound.
  f_equal. remember (N.to_nat w). rewrite <- N_nat_Z. rewrite <- Heqn. clear.
  revert v. induction n; intros; cbn [le_to_lbool']; auto.
  rewrite nil_le_to_lbool'. rewrite (nil_le_to_lbool' _ _ [Z.odd v]). f_equal.
  - rewrite <- (IHn (v / 2)). f_equal. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia. rewrite Z.rem_mul_r; try lia.
    rewrite Z.mul_comm. rewrite Z.div_add by lia.
    rewrite Zmod_div. lia.
  - f_equal. apply Z_odd_pow_2_S.
Qed.

Lemma to_lbool_bit_mod: forall w v,
    to_lbool w (BitArith.mod_bound w v) = to_lbool w v.
Proof.
  intros.
  unfold to_lbool.
  match goal with
  | |- ?x = ?y =>
      cut (rev (rev x) = rev (rev y));
      [now rewrite !rev_involutive|]
  end.
  pose proof (le_to_lbool_bit_mod w v).
  unfold le_to_lbool in H.
  congruence.
Qed.

Lemma le_to_lbool_bit_plus: forall w v1 v2,
    le_to_lbool w (BitArith.plus_mod w v1 v2) = le_to_lbool w (v1 + v2).
Proof. intros. unfold BitArith.plus_mod. now rewrite le_to_lbool_bit_mod. Qed.

Lemma le_to_lbool_bit_minus: forall w v1 v2,
    le_to_lbool w (BitArith.minus_mod w v1 v2) = le_to_lbool w (v1 - v2).
Proof. intros. unfold BitArith.minus_mod. now rewrite le_to_lbool_bit_mod. Qed.

Lemma le_to_lbool_bit_mult: forall w v1 v2,
    le_to_lbool w (BitArith.mult_mod w v1 v2) = le_to_lbool w (v1 * v2).
Proof. intros. unfold BitArith.mult_mod. now rewrite le_to_lbool_bit_mod. Qed.

Lemma Z_pow_double_ltb: forall (a m: Z) (b: bool),
    0 < m -> a <? m = (a * 2 + (if b then 1 else 0) <? 2 * m).
Proof.
  intros. destruct (a <? m) eqn:?H; destruct b.
  - rewrite Z.ltb_lt in H0. assert (a * 2 + 1 < 2 * m) by lia.
    rewrite <- Z.ltb_lt in H1. now rewrite H1.
  - rewrite Z.ltb_lt in H0. rewrite Z.add_0_r.
    assert (a * 2 < 2 * m) by lia. rewrite <- Z.ltb_lt in H1. now rewrite H1.
  - rewrite Z.ltb_ge in H0. assert (2 * m <= a * 2 + 1) by lia.
    rewrite <- Z.ltb_ge in H1. now rewrite H1.
  - rewrite Z.ltb_ge in H0. rewrite Z.add_0_r. assert (2 * m <= a * 2) by lia.
    rewrite <- Z.ltb_ge in H1. now rewrite H1.
Qed.

Lemma int_mod_bound_succ_div2:
  forall (p : positive) (v : Z),
    IntArith.mod_bound p (v / 2) * 2 + (if Z.odd v then 1 else 0) =
      IntArith.mod_bound (Pos.succ p) v.
Proof.
  intros p v. unfold IntArith.mod_bound, IntArith.upper_bound, IntArith.mod_amt.
  rewrite Pos2Z.inj_succ. rewrite Z.pow_succ_r by lia. rewrite <- Z.add_1_r.
  remember (Z.pos p). rewrite Z.add_simpl_r. rewrite <- div_2_mod_2_pow by lia.
  replace (2 ^ z) with (2 ^ Z.succ (z - 1)) at 6 by (f_equal; lia).
  rewrite Z.pow_succ_r by lia. rewrite <- Z_pow_double_ltb.
  - destruct ((v / 2) mod 2 ^ z <? 2 ^ (z - 1)); lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma int_from_to_bool: forall w v,
    IntArith.le_from_lbool (le_to_lbool w v) =
      (w, if (w =? 0)%N then 0 else IntArith.mod_bound (pos_of_N w) v).
Proof.
  intros. unfold le_to_lbool. unfold IntArith.le_from_lbool.
  rewrite Zlength_rev, Zlength_to_lbool', Zlength_nil. f_equal. 1: lia.
  destruct (w =? 0)%N eqn: ?H. 1: rewrite N.eqb_eq in H; subst; now simpl.
  rewrite N.eqb_neq in H.
  assert (pos_of_N w = Pos.of_nat (N.to_nat w)). {
    destruct w; simpl; auto. now rewrite Pos2Nat.id. } rewrite H0. clear H0.
  remember (N.to_nat w). assert (n <> O) by lia. clear H Heqn w. revert v.
  induction n; intros.
  - exfalso. now apply H0.
  - simpl. destruct n.
    + simpl. unfold IntArith.mod_bound, IntArith.upper_bound, IntArith.mod_amt.
      rewrite Z.pow_1_r, Z.sub_diag, Z.pow_0_r. rewrite Zmod_odd.
      destruct (Z.odd v); now simpl.
    + rewrite nil_le_to_lbool'. rewrite rev_app_distr. cbn [rev app].
      rewrite IntArith.lbool_to_val_cons; auto.
      * simpl Z.shiftl. rewrite Z.add_0_l. rewrite IntArith.lbool_to_val_1_0.
        assert (S n <> O) by lia. specialize (IHn H). rewrite IHn.
        remember (Pos.of_nat (S n)). apply int_mod_bound_succ_div2.
      * intro. assert (Zlength (rev (le_to_lbool' (S n) (v / 2) [])) = 0). {
          rewrite H. apply Zlength_nil. }
        rewrite Zlength_rev, Zlength_to_lbool', Zlength_nil in H1. lia.
Qed.

Lemma le_to_lbool_int_mod: forall w v,
    le_to_lbool w (IntArith.mod_bound (pos_of_N w) v) = le_to_lbool w v.
Proof.
  intros. unfold le_to_lbool.
  assert (pos_of_N w = Pos.of_nat (N.to_nat w)). {
    destruct w; simpl; auto. now rewrite Pos2Nat.id. } rewrite H. clear H.
  remember (N.to_nat w). f_equal. clear Heqn w. revert v. induction n; intros.
  1: now simpl. cbn [le_to_lbool']. rewrite nil_le_to_lbool'.
  rewrite (nil_le_to_lbool' _ _ [Z.odd v]). f_equal.
  - destruct n. 1: now simpl. rewrite <- (IHn (v / 2)). f_equal. clear.
    unfold IntArith.mod_bound, IntArith.upper_bound, IntArith.mod_amt.
    rewrite (Nat2Pos.inj_succ (S n)) by lia. rewrite Pos2Z.inj_succ.
    remember (Z.pos (Pos.of_nat (S n))). assert (1 <= z) by lia. clear Heqz.
    replace (2 ^ (Z.succ z - 1)) with (2 ^ Z.succ (z - 1)) by (f_equal; lia).
    rewrite !Z.pow_succ_r by lia. rewrite <- div_2_mod_2_pow by lia.
    rewrite <- Z_pow_double_ltb. 2: apply Z.pow_pos_nonneg; lia.
    assert ((if Z.odd v then 1 else 0) / 2 = 0) by (now destruct (Z.odd v)).
    destruct ((v / 2) mod 2 ^ z <? 2 ^ (z - 1)).
    + rewrite Z.div_add_l by lia. rewrite H0. lia.
    + rewrite Z.add_sub_swap, (Z.mul_comm 2 (2 ^ z)), <- Z.mul_sub_distr_r.
      rewrite Z.div_add_l by lia. rewrite H0. lia.
  - unfold IntArith.mod_bound, IntArith.upper_bound, IntArith.mod_amt. f_equal.
    replace (Z.pos (Pos.of_nat (S n))) with (Z.of_nat (S n)) by lia.
    destruct (v mod 2 ^ Z.of_nat (S n) <? 2 ^ (Z.of_nat (S n) - 1)).
    1: apply Z_odd_pow_2_S. rewrite Z.odd_sub.
    rewrite Z_odd_pow_2_S. rewrite <- (Z.add_0_l (2 ^ Z.of_nat (S n))).
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. rewrite Z.odd_add_mul_2.
    simpl. apply xorb_false_r.
Qed.

Lemma le_to_lbool_int_plus: forall w v1 v2,
    le_to_lbool w (IntArith.plus_mod (pos_of_N w) v1 v2) = le_to_lbool w (v1 + v2).
Proof. intros. unfold IntArith.plus_mod. now rewrite le_to_lbool_int_mod. Qed.

Lemma le_to_lbool_int_minus: forall w v1 v2,
    le_to_lbool w (IntArith.minus_mod (pos_of_N w) v1 v2) = le_to_lbool w (v1 - v2).
Proof. intros. unfold IntArith.minus_mod. now rewrite le_to_lbool_int_mod. Qed.

Lemma le_to_lbool_int_mult: forall w v1 v2,
    le_to_lbool w (IntArith.mult_mod (pos_of_N w) v1 v2) = le_to_lbool w (v1 * v2).
Proof. intros. unfold IntArith.mult_mod. now rewrite le_to_lbool_int_mod. Qed.

Lemma pos_N_nat: forall n, pos_of_N (N.of_nat n) = Pos.of_nat n.
Proof.
  induction n; simpl; auto. destruct n. 1: now simpl. simpl in IHn. simpl. now f_equal.
Qed.

Lemma int_le_to_lbool_back: forall w v,
    IntArith.lbool_to_val (le_to_lbool w v) 1 0 =
      if N.eqb w N0 then 0 else IntArith.mod_bound (pos_of_N w) v.
Proof.
  intros. destruct (w =? 0)%N eqn:?H.
  - rewrite N.eqb_eq in H. subst w. now simpl.
  - rewrite N.eqb_neq in H. unfold le_to_lbool. rewrite <- Nnat.N2Nat.id at 2.
    remember (N.to_nat w).
    rewrite pos_N_nat. assert (O < n)%nat by lia. clear w H Heqn. revert v.
    induction n. 1: exfalso; lia. intros. simpl. destruct n.
    + simpl. unfold IntArith.mod_bound, IntArith.mod_amt, IntArith.upper_bound. simpl.
      unfold Z.pow_pos. simpl. rewrite Zmod_odd. destruct (Z.odd v); simpl; auto.
    + rewrite nil_le_to_lbool'. rewrite rev_app_distr. simpl rev at 1. cbn [app].
      rewrite IntArith.lbool_to_val_cons.
      * simpl Z.shiftl. rewrite Z.add_0_l. rewrite IntArith.lbool_to_val_1_0.
        rewrite IHn by lia. remember (Pos.of_nat (S n)). apply int_mod_bound_succ_div2.
      * intro. pose proof (Zlength_nil bool). rewrite <- H in H1.
        rewrite Zlength_rev in H1. rewrite Zlength_to_lbool' in H1.
        rewrite Zlength_nil in H1. lia.
Qed.

Lemma int_to_lbool_back: forall w v,
    IntArith.lbool_to_val (rev (to_lbool w v)) 1 0 =
      if N.eqb w N0 then 0 else IntArith.mod_bound (pos_of_N w) v.
Proof.
  apply int_le_to_lbool_back.
Qed.

Lemma bit_le_to_lbool_back: forall w v,
    BitArith.lbool_to_val (le_to_lbool w v) 1 0 = BitArith.mod_bound w v.
Proof.
  intros. unfold le_to_lbool. rewrite <- Nnat.N2Nat.id at 2. remember (N.to_nat w).
  clear . revert v. induction n; intros; simpl.
  - unfold BitArith.mod_bound, BitArith.upper_bound. simpl. now rewrite Z.mod_1_r.
  - rewrite nil_le_to_lbool'. rewrite rev_app_distr. simpl rev at 1.
    rewrite BitArith.lbool_to_val_app. simpl. rewrite BitArith.lbool_to_val_1_0.
    rewrite IHn by lia. unfold BitArith.mod_bound, BitArith.upper_bound.
    rewrite N2Z.inj_pos. rewrite nat_N_Z. rewrite Zpos_P_of_succ_nat.
    rewrite Z.pow_succ_r by lia. apply div_2_mod_2_pow. lia.
Qed.

Lemma bit_to_lbool_back: forall w v,
    BitArith.lbool_to_val (rev (to_lbool w v)) 1 0 = BitArith.mod_bound w v.
Proof.
  apply bit_le_to_lbool_back.
Qed.

(*
  Compute (le_to_lbool (4)%N (-6)).
  Compute (le_to_lbool (8)%N (-7)).
  Compute (le_to_lbool (2)%N (-7)).
  Compute (le_to_lbool (8)%N (7)).
  Compute (le_to_lbool (8)%N (0)).
  Compute (IntArith.le_from_lbool (le_to_lbool (4)%N (-8))).
  Compute (IntArith.le_from_lbool (le_to_lbool (4)%N (-15))).
  Compute (IntArith.le_from_lbool (le_to_lbool (4)%N (8))).
  Compute (BitArith.le_from_lbool (le_to_lbool (4)%N (8))).
  Compute (BitArith.le_from_lbool (le_to_lbool (4)%N (17))).
  Compute (BitArith.le_from_lbool (le_to_lbool (4)%N (-1))).

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

Module P4ArithTactics.
  Ltac unfold_bit_operation :=
    match goal with
    | |- context [ BitArith.bit_not _ _ ] => unfold BitArith.bit_not
    | |- context [ BitArith.neg _ _ ] => unfold BitArith.neg
    | |- context [ BitArith.plus_sat _ _ ] => unfold BitArith.plus_sat
    | |- context [ BitArith.plus_mod _ _ ] => unfold BitArith.plus_mod
    | |- context [ BitArith.minus_mod _ _ ] => unfold BitArith.minus_mod
    | |- context [ BitArith.mult_mod _ _ ] => unfold BitArith.mult_mod
    | |- context [ BitArith.shift_right _ _ ] => unfold BitArith.shift_right
    | |- context [ BitArith.shift_left _ _ ] => unfold BitArith.shift_left
    | |- context [ BitArith.bit_and _ _ ] => unfold BitArith.bit_and
    | |- context [ BitArith.bit_xor _ _ ] => unfold BitArith.bit_xor
    | |- context [ BitArith.bit_or _ _ ] => unfold BitArith.bit_or
    | |- context [ BitArith.concat _ _ _ _ ] => unfold BitArith.concat
    end.

  Ltac bit_bounded :=
    try unfold_bit_operation;
    try apply BitArith.sat_bound_bound;
    try apply BitArith.mod_bound_bound; try lia.

  Ltac unfold_int_operation :=
    match goal with
    | |- context [ IntArith.bit_not _ _ ] => unfold IntArith.bit_not
    | |- context [ IntArith.neg _ _ ] => unfold IntArith.neg
    | |- context [ IntArith.plus_sat _ _ ] => unfold IntArith.plus_sat
    | |- context [ IntArith.minus_sat _ _ ] => unfold IntArith.minus_sat
    | |- context [ IntArith.plus_mod _ _ ] => unfold IntArith.plus_mod
    | |- context [ IntArith.minus_mod _ _ ] => unfold IntArith.minus_mod
    | |- context [ IntArith.mult_mod _ _ ] => unfold IntArith.mult_mod
    | |- context [ IntArith.shift_right _ _ ] => unfold IntArith.shift_right
    | |- context [ IntArith.shift_left _ _ ] => unfold IntArith.shift_left
    | |- context [ IntArith.bit_and _ _ ] => unfold IntArith.bit_and
    | |- context [ IntArith.bit_xor _ _ ] => unfold IntArith.bit_xor
    | |- context [ IntArith.bit_or _ _ ] => unfold IntArith.bit_or
    | |- context [ IntArith.concat _ _ _ _ ] => unfold IntArith.concat
    end.

  Ltac int_bounded :=
    try unfold_bit_operation;
    try apply IntArith.sat_bound_bound;
    try apply IntArith.mod_bound_bound; try lia.
End P4ArithTactics.
