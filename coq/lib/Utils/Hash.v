Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Require Import Poulet4.P4light.Semantics.Bitwise.
Require Import Poulet4.Utils.CoqLib.

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
    little_to_big (of_N poly out_width).

  Definition init_bits : Bits :=
    little_to_big (of_N init out_width).

  Definition xor_out_bits : Bits :=
    little_to_big (of_N xor_out out_width).

  Definition in_width_round : nat := (in_width + 7) / 8 * 8.

  Lemma in_width_le_round: in_width <= in_width_round.
  Proof.
    unfold in_width_round. generalize in_width. clear. induction n.
    - simpl. lia.
    - rewrite <- Nat.add_1_r, <- Nat.add_assoc. change (1 + 7) with 8.
      rewrite <- (Nat.mul_1_l 8) at 1. rewrite Nat.div_add by auto.
      rewrite Nat.mul_add_distr_r. rewrite (Nat.div_mod_eq n 8) at 1.
      rewrite (Nat.mul_comm 8), <- Nat.add_assoc, <- Nat.add_le_mono_l. simpl "*".
      assert (0 <= n mod 8 < 8) by
        (apply Nat.mod_bound_pos; [apply Nat.le_0_l | apply Nat.lt_0_succ]). lia.
  Qed.

  Definition group_list {A : Type} (l : list A) (n : nat) : list (list A) :=
    let group_list' (i : A) (acc_n_m : list (list A) * (nat * nat)) :=
      let '(acc, (n, m)) := acc_n_m in
      match m, acc with
      | O, _  => ([i] :: acc, (n, n))
      | S m', hd :: tl => ((i :: hd) :: tl, (n, m'))
      (* never hit *)
      | _, _ => (acc, (n, m))
      end
    in fst (fold_right group_list' ([], (n-1, O)) l).

  Lemma concat_group_list {A: Type}: forall n (l: list A), concat (group_list l n) = l.
  Proof.
    clear. intros n l. unfold group_list. remember (fun (i : _) (acc_n_m : _) => _) as f.
    assert (Hh: forall o acc acc' a a' m m',
               (0 < m -> acc <> []) ->
               fold_right f (acc, (a, m)) o = (acc', (a', m')) ->
               concat acc' = o ++ concat acc /\ (0 < m' -> acc' <> [])). {
      induction o as [|e o]; intros acc acc' a a' m m' Hn Hf; simpl in Hf |- *.
      - inversion Hf; subst. split; [reflexivity | assumption].
      - destruct (fold_right f (acc, (a, m)) o) as [acc2 [a2 m2]] eqn: Hfd.
        specialize (IHo _ _ _ _ _ _ Hn Hfd). destruct IHo as [IHo Hn'].
        rewrite Heqf in Hf. destruct m2.
        + inversion Hf; subst. simpl. rewrite IHo.
          split; [reflexivity | intros _ He; inversion He].
        + destruct acc2.
          * specialize (Hn' ltac:(lia)). exfalso. apply Hn'. reflexivity.
          * inversion Hf; subst. simpl in IHo |- *. rewrite IHo.
            split; [reflexivity | intros _ He; inversion He]. }
    destruct (fold_right f ([], (n - 1, 0)) l) as [acc' [a' m']] eqn: Hf.
    specialize (Hh _ _ _ _ _ 0 _ ltac:(intros; lia) Hf). destruct Hh as [Hh _].
    simpl in *. rewrite Hh. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma map_group_list: forall {A B: Type} (f: A -> B) (l: list A) s,
      group_list (map f l) s = map (map f) (group_list l s).
  Proof.
    clear. intros A B f l s. unfold group_list.
    remember (fun (T: Type) (i : T) (acc_n_m : list (list T) * (nat * nat)) =>
       match acc_n_m with
       | (acc, (n, 0)) => ([i] :: acc, (n, n))
       | (acc, (n, S m' as m)) =>
           match acc with
           | [] => (acc, (n, m))
           | hd :: tl => ((i :: hd) :: tl, (n, m'))
           end
       end) as g eqn: Hg.
    remember (fun (i : B) (acc_n_m : _) => _) as g1.
    remember (fun (i : A) (acc_n_m : _) => _) as g2.
    rewrite (fold_right_ext g1 (g B)) by (intros; rewrite Heqg1, Hg; reflexivity).
    rewrite (fold_right_ext g2 (g A)) by (intros; rewrite Heqg2, Hg; reflexivity).
    clear dependent g1. clear dependent g2.
    assert (Hh: forall o acc acc1 acc2 a a1 a2 m m1 m2,
               (0 < m -> acc <> []) ->
               fold_right (g A) (acc, (a, m)) o = (acc1, (a1, m1)) ->
               fold_right (g B) (map (map f) acc, (a, m)) (map f o) = (acc2, (a2, m2)) ->
               a1 = a2 /\ m1 = m2 /\ acc2 = map (map f) acc1 /\ (0 < m1 -> acc1 <> [])). {
      induction o as [|e o]; intros acc acc1 acc2 a a1 a2 m m1 m2 Hn Hf Hfm;
        simpl in Hf, Hfm |- *.
      - inversion Hf. subst. inversion Hfm. subst. intuition.
      - destruct (fold_right (g A) (acc, (a, m)) o) as [acc1' [a1' m1']] eqn: Hfd.
        destruct (fold_right (g B) (map (map f) acc, (a, m)) (map f o))
          as [acc2' [a2' m2']] eqn: Hfmd. specialize (IHo _ _ _ _ _ _ _ _ _ Hn Hfd Hfmd).
        destruct IHo as [Ha [Hm [Hacc Hn']]]. subst a2' m2' acc2'. clear Hfd Hfmd.
        subst. destruct m1'.
        + inversion Hf; subst; clear Hf. inversion Hfm; subst; clear Hfm. simpl.
          intuition. inversion H0.
        + destruct acc1'. 1: exfalso; apply Hn'; [lia | reflexivity].
          inversion Hf; subst; clear Hf. simpl in Hfm.
          inversion Hfm; subst; clear Hfm. simpl. intuition. inversion H0. }
    destruct (fold_right (g A) ([], (s - 1, 0)) l) as [acc1 [a1 m1]] eqn: Hf.
    destruct (fold_right (g B) ([], (s - 1, 0)) (map f l)) as [acc2 [a2 m2]] eqn: Hfm.
    simpl. specialize (Hh _ _ _ _ _ _ _ 0 _ _ ltac:(intros; lia) Hf Hfm).
    destruct Hh as [_ [_ [Hh _]]]. assumption.
  Qed.

  Definition input_bits : Bits :=
    let input_round :=
      zero (in_width_round - in_width) ++ input in
    let input_rev :=
      if refin
      then concat (map (@rev bool) (group_list input_round 8))
      else input_round in
    let input_padded := (zero out_width) ++ input_rev in
      xor init_bits (little_to_big input_padded).

  Fixpoint compute_crc' (bits: Bits) (i: nat) :=
    if i <=? out_width then bits
    else
      match i with
      | S i' =>
          match bits with
          | false :: bits' => compute_crc' bits' i'
          | true :: bits' => compute_crc' (xor poly_bits bits') i'
          (* never hit *)
          | [] => []
          end
      (* never hit *)
      | O => []
      end.

  Definition compute_crc : Bits :=
    let crc_output := compute_crc' input_bits (length input_bits) in
    let crc_rev := if refout then rev crc_output else crc_output in
    big_to_little (xor xor_out_bits crc_rev).

  Lemma length_xor_out_bits: length xor_out_bits = out_width.
  Proof.
    unfold xor_out_bits. now rewrite rev_length, of_N_length.
  Qed.

  Lemma length_poly_bits: length poly_bits = out_width.
  Proof.
    unfold poly_bits. now rewrite rev_length, of_N_length.
  Qed.

  Lemma length_compute_crc': forall bits i,
      i = length bits ->
      length (compute_crc' bits i) = if (i <=? out_width) then (length bits) else out_width.
  Proof.
    intros bits i Hl. revert bits Hl. induction i; intros.
    - simpl. auto.
    - unfold compute_crc'. fold compute_crc'. destruct (S i <=? out_width) eqn : Hle; auto.
      destruct bits; simpl in Hl. 1: inversion Hl.
      apply Nat.succ_inj in Hl. rewrite Nat.leb_gt in Hle.
      rewrite Nat.lt_succ_r in Hle. apply Nat.lt_eq_cases in Hle. destruct Hle as [Hlt | Heq].
      + rewrite <- Nat.leb_gt in Hlt.
        destruct b; rewrite IHi; auto; try (now rewrite Hlt).
        rewrite xor_length. rewrite length_poly_bits.
        rewrite Nat.leb_gt in Hlt. subst i.
        rewrite Nat.max_r; auto. apply Nat.lt_le_incl; auto.
      + assert (length (xor poly_bits bits) = i). {
          unfold xor. rewrite map2_length, <- Hl, length_poly_bits, Heq.
          apply Nat.max_id. }
        destruct b; rewrite IHi; auto; rewrite Heq, Nat.leb_refl; auto.
  Qed.

  Lemma length_compute_crc: length compute_crc = out_width.
  Proof.
    unfold compute_crc. rewrite rev_length. rewrite xor_length.
    cut (max (length xor_out_bits)
             (length (compute_crc' input_bits (length input_bits))) = out_width).
    - intros. destruct refout; auto. rewrite rev_length; auto.
    - rewrite length_xor_out_bits. rewrite length_compute_crc'; auto.
      destruct (_ <=? _) eqn:?Hle.
      + rewrite Nat.leb_le in Hle. rewrite Nat.max_l; auto.
      + apply Nat.max_id.
  Qed.

  Lemma length_init_bits: length init_bits = out_width.
  Proof.
    unfold init_bits. rewrite rev_length, of_N_length. reflexivity.
  Qed.

  Lemma length_input_bits: length input_bits = out_width + in_width_round.
  Proof.
    unfold input_bits.
    rewrite xor_length, rev_length, app_length, length_init_bits, length_zero.
    rewrite <- (Nat.add_0_r out_width) at 1. rewrite Nat.add_max_distr_l, Nat.max_0_l.
    f_equal. destruct refin.
    - rewrite length_concat_map_rev, concat_group_list, app_length, length_zero.
      fold in_width. rewrite Nat.sub_add; auto. apply in_width_le_round.
    - rewrite app_length, length_zero. fold in_width. rewrite Nat.sub_add; auto.
      apply in_width_le_round.
  Qed.

End CRC.

Section CRC_XOR.

  Variable (out_width : nat).
  Variable (poly : N).
  Variable (init : N).
  Variable (xor_out : N).
  Variable (refin : bool).
  Variable (refout : bool).

  Infix "⦻" := xor (at level 38, left associativity).

  Notation input := (input_bits out_width init refin) (only parsing).

  Lemma concat_rev_group_pos_manip: forall n,
      pos_manip_func (fun l : list bool => concat (map (rev (A:=bool)) (group_list l n))).
  Proof.
    intros s. red. intros n. exists (concat (map (@rev nat) (group_list (seq 0 n) s))).
    intros b l Hl. rewrite concat_map, map_map.
    assert (Heql: l = map (fun i => nth i l b) (seq 0 (length l))). {
      clear. induction l using rev_ind.
      - simpl. reflexivity.
      - rewrite app_length. simpl. replace (length l + 1) with (S (length l)) by lia.
        rewrite seq_S, map_app. simpl. rewrite app_nth2; auto. rewrite Nat.sub_diag.
        simpl. f_equal. rewrite IHl at 1. apply map_ext_Forall. clear.
        rewrite Forall_forall. intros i Hin. rewrite in_seq in Hin. simpl in Hin.
        rewrite app_nth1; auto. destruct Hin; assumption. }
    rewrite Heql at 1. rewrite map_group_list, map_map, Hl. f_equal. apply map_ext.
    intros ll. rewrite map_rev. reflexivity.
  Qed.

  Lemma input_bits_xor_affine: forall a b c,
      length a = length b -> length b = length c ->
      input (a ⦻ b ⦻ c) = input a ⦻ input b ⦻ input c.
  Proof.
    intros a b c Hab Hbc. unfold input_bits. rewrite xor_affine. f_equal.
    assert (Hwxy: forall x y,
               length x = length y ->
               in_width_round x - in_width x = in_width_round y - in_width y). {
      intros x y Hxy. unfold in_width_round, in_width. rewrite Hxy. reflexivity. }
    assert (Hlxy: forall x y, length x = length y ->
                         length (zero (in_width_round x - in_width x) ++ x) =
                           length (zero (in_width_round y - in_width y) ++ y)). {
      intros x y Hxy. unfold in_width_round, in_width.
      rewrite !app_length, !length_zero, Hxy. reflexivity. }
    unfold little_to_big. rewrite <- !xor_rev_linear.
    2, 3: rewrite ?xor_length, !app_length, ?Nat.add_max_distr_l, ?Nat.add_cancel_l;
    destruct refin; [rewrite !length_concat_map_rev, !concat_group_list |];
    rewrite (Hlxy a b), ?(Hlxy b c), ?Nat.max_id; easy.
    f_equal. rewrite <- !zero_app_xor_linear. f_equal. destruct refin.
    - remember (fun l => concat (map (rev (A:=bool)) (group_list l 8))) as f eqn: Hf.
      replace (concat (_ _ (_ (_ _ ++ a ⦻ b ⦻ c) 8))) with
        (f (zero (in_width_round (a ⦻ b ⦻ c) - in_width (a ⦻ b ⦻ c)) ++ a ⦻ b ⦻ c))
        by now rewrite Hf.
      replace (concat (_ _ (_ (_ _ ++ a) 8))) with
        (f (zero (in_width_round a - in_width a) ++ a)) by now rewrite Hf.
      replace (concat (_ _ (_ (_ _ ++ b) 8))) with
        (f (zero (in_width_round b - in_width b) ++ b)) by now rewrite Hf.
      replace (concat (_ _ (_ (_ _ ++ c) 8))) with
        (f (zero (in_width_round c - in_width c) ++ c)) by now rewrite Hf.
      assert (pos_manip_func f) by (subst; apply concat_rev_group_pos_manip).
      rewrite <- !pos_manip_func_xor_linear; auto.
      2: rewrite xor_length, (Hlxy a b), (Hlxy b c), Nat.max_id; auto.
      f_equal. rewrite (Hwxy a b), (Hwxy b c), <- !zero_app_xor_linear; auto.
      do 2 f_equal. apply Hwxy. rewrite !xor_length, Hab, Hbc, !Nat.max_id. reflexivity.
    - rewrite (Hwxy a b), !(Hwxy b c), <- !zero_app_xor_linear; auto. do 2 f_equal.
      apply Hwxy. rewrite !xor_length, Hab, Hbc, !Nat.max_id. reflexivity.
  Qed.

  Lemma compute_crc'_xor_affine: forall n a b c,
      length a = n -> length b = n -> length c = n ->
      compute_crc' out_width poly (a ⦻ b ⦻ c) n =
        compute_crc' out_width poly a n ⦻
          compute_crc' out_width poly b n ⦻
          compute_crc' out_width poly c n.
  Proof.
    intros m a b c Hla Hlb Hlc. revert a b c Hla Hlb Hlc out_width.
    induction m; intros a b c Hla Hlb Hlc out_width.
    - destruct a. 2: simpl in Hla; inversion Hla.
      destruct b. 2: simpl in Hlb; inversion Hlb.
      destruct c. 2: simpl in Hlc; inversion Hlc. simpl. reflexivity.
    - destruct a as [|a ra]; simpl in Hla. 1: inversion Hla.
      destruct b as [|b rb]; simpl in Hlb. 1: inversion Hlb.
      destruct c as [|c rc]; simpl in Hlc. 1: inversion Hlc.
      inversion Hla. clear Hla. rename H0 into Hla.
      inversion Hlb. clear Hlb. rename H0 into Hlb.
      inversion Hlc. clear Hlc. rename H0 into Hlc.
      rewrite !xor_cons. simpl. destruct out_width.
      + remember (poly_bits 0 poly) as p. pose proof (length_poly_bits 0 poly) as Hp.
        rewrite <- Heqp in Hp. destruct p. 2: simpl in Hp; inversion Hp. rewrite !xor_nil_l.
        rewrite Hla. destruct (xorb (xorb a b) c), a, b, c; apply IHm; auto.
      + rewrite Hla. destruct (m <=? n) eqn: Hmn. 1: rewrite !xor_cons; reflexivity.
        remember (poly_bits (S n) poly) as p. pose proof (length_poly_bits (S n) poly) as Hp.
        rewrite <- Heqp in Hp. rewrite Nat.leb_gt in Hmn.
        assert (length (p ⦻ ra) = m) as Hra by (rewrite xor_length; lia).
        assert (length (p ⦻ rb) = m) as Hrb by (rewrite xor_length; lia).
        assert (length (p ⦻ rc) = m) as Hrc by (rewrite xor_length; lia).
        destruct a, b, c; simpl; rewrite <- IHm; auto.
        * rewrite xor_affine. reflexivity.
        * rewrite <- xor_assoc, (xor_assoc p), (xor_comm ra p), <- !xor_assoc,
            xor_nilpotent, xor_false_l; [reflexivity | lia].
        * rewrite <- xor_assoc, (xor_comm (p ⦻ ra ⦻ rb)), <- !xor_assoc,
            xor_nilpotent, xor_false_l; [reflexivity | lia].
        * rewrite <- !xor_assoc. reflexivity.
        * rewrite <- !xor_assoc, (xor_comm ra p), (xor_comm (p ⦻ ra ⦻ rb)), <- !xor_assoc,
            xor_nilpotent, xor_false_l; [reflexivity | lia].
        * rewrite <- !xor_assoc, (xor_comm ra p). reflexivity.
        * rewrite <- !xor_assoc, (xor_comm (ra ⦻ rb)), <- !xor_assoc. reflexivity.
  Qed.

  Notation CRC := (compute_crc out_width poly init xor_out refin refout) (only parsing).

  Lemma compute_crc_xor_affine: forall a b c,
      length a = length b -> length b = length c ->
      CRC (a ⦻ b ⦻ c) = CRC a ⦻ CRC b ⦻ CRC c.
  Proof.
    intros a b c Hab Hbc. unfold compute_crc.
    assert (Hl: forall x, length (compute_crc' out_width poly (input_bits out_width init refin x)
                               (length (input_bits out_width init refin x))) = out_width). {
      intros. rewrite length_compute_crc'; auto. rewrite length_input_bits.
      destruct (_ <=? _) eqn: Hle; auto. rewrite Nat.leb_le in Hle. lia. }
    remember (compute_crc' _ _ (_ _ _ _ (a ⦻ b ⦻ c)) _) as rl eqn: Hrl.
    remember (compute_crc' _ _ (_ _ _ _ a) _) as ra eqn: Hra.
    remember (compute_crc' _ _ (_ _ _ _ b) _) as rb eqn: Hrb.
    remember (compute_crc' _ _ (_ _ _ _ c) _) as rc eqn: Hrc.
    remember (_ _ xor_out) as x eqn: Hx.
    remember (if refout then rev rl else rl) as ll.
    remember (if refout then rev ra else ra) as aa.
    remember (if refout then rev rb else rb) as bb.
    remember (if refout then rev rc else rc) as cc.
    rewrite <- !xor_rev_linear.
    2, 3: rewrite !xor_length; subst; rewrite length_xor_out_bits;
    destruct refout; rewrite ?rev_length, !Hl, !Nat.max_id; reflexivity.
    rewrite xor_affine. unfold big_to_little. do 2 f_equal.
    cut (rl = ra ⦻ rb ⦻ rc).
    - intros He. subst ll aa bb cc. destruct refout; auto. rewrite <- !xor_rev_linear.
      2, 3: rewrite ?xor_length; subst; destruct refout;
      rewrite !Hl, ?Nat.max_id; reflexivity. f_equal. assumption.
    - subst. rewrite !length_input_bits. unfold in_width_round, in_width.
      rewrite !xor_length. rewrite <- Hbc, <- Hab, !Nat.max_id.
      rewrite <- compute_crc'_xor_affine.
      2, 3, 4:  rewrite length_input_bits; unfold in_width_round, in_width;
      rewrite <- ?Hbc, <- ?Hab; reflexivity. f_equal.
      rewrite input_bits_xor_affine; auto.
  Qed.

End CRC_XOR.

Module CRC_CHECK.

  Local Open Scope hex_N_scope.

  Definition Nnth (i: nat) (l: list N) := nth i l 0.
  Definition Bnth (i: nat) (l: list bool) := nth i l false.

  (* The following checks come from https://crccalc.com *)

  Definition data := Eval vm_compute in of_N 0x313233343536373839 72.

  Definition CRC8_Poly := [0x07; 0x9B; 0x39; 0xD5; 0x1D; 0x1D; 0x07; 0x31; 0x07; 0x9B].
  Definition CRC8_Init := [0x00; 0xFF; 0x00; 0x00; 0xFF; 0xFD; 0x00; 0x00; 0xFF; 0x00].
  Definition CRC8_RefIn := [false; false; true; false; true; false; false; true; true; true].
  Definition CRC8_XorOut := [0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x55; 0x00; 0x00; 0x00].
  Definition CRC8_Check := [0xF4; 0xDA; 0x15; 0xBC; 0x97; 0x7E; 0xA1; 0xA1; 0xD0; 0x25].

  Lemma CRC8_Correct:
    map (fun i => to_N (compute_crc 8 (Nnth i CRC8_Poly) (Nnth i CRC8_Init) (Nnth i CRC8_XorOut)
                       (Bnth i CRC8_RefIn) (Bnth i CRC8_RefIn) data))
      (seq 0 (length CRC8_Poly)) = CRC8_Check.
  Proof. reflexivity. Qed.

  Definition CRC16_Poly := [0x8005; 0x1021; 0x8005; 0x1021; 0xC867; 0x8005; 0x0589; 0x0589;
                            0x3D65; 0x3D65; 0x1021; 0x1021; 0x8005; 0x1021; 0x8005; 0x1021;
                            0x8BB7; 0xA097; 0x1021; 0x8005; 0x1021; 0x1021; 0x1021].
  Definition CRC16_Init := [0x0000; 0x1D0F; 0x0000; 0xFFFF; 0xFFFF; 0x800D; 0x0000; 0x0000;
                            0x0000; 0x0000; 0xFFFF; 0x0000; 0x0000; 0xFFFF; 0xFFFF; 0xB2AA;
                            0x0000; 0x0000; 0x89EC; 0xFFFF; 0xFFFF; 0x0000; 0xC6C6].
  Definition CRC16_RefIn := [true; false; false; false; false; false; false; false; true;
                             false; false; true; true; true; true; true; false; false; true;
                             true; true; false; true].
  Definition CRC16_XorOut := [0x0000; 0x0000; 0x0000; 0x0000; 0x0000; 0x0000; 0x0001; 0x0000;
                              0xFFFF; 0xFFFF; 0xFFFF; 0x0000; 0xFFFF; 0x0000; 0x0000; 0x0000;
                              0x0000; 0x0000; 0x0000; 0xFFFF; 0xFFFF; 0x0000; 0x0000].
  Definition CRC16_Check := [0xBB3D; 0xE5CC; 0xFEE8; 0x29B1; 0x4C06; 0x9ECF; 0x007E; 0x007F;
                             0xEA82; 0xC2B7; 0xD64E; 0x2189; 0x44C2; 0x6F91; 0x4B37; 0x63D0;
                             0xD0DB; 0x0FB3; 0x26B1; 0xB4C8; 0x906E; 0x31C3; 0xBF05].

  Lemma CRC16_Correct:
    map (fun i => to_N (compute_crc 16 (Nnth i CRC16_Poly) (Nnth i CRC16_Init)
                       (Nnth i CRC16_XorOut) (Bnth i CRC16_RefIn) (Bnth i CRC16_RefIn) data))
      (seq 0 (length CRC16_Poly)) = CRC16_Check.
  Proof. vm_compute. reflexivity. Qed.

  Definition CRC32_Poly := [0x04C11DB7; 0x04C11DB7; 0x04C11DB7; 0x04C11DB7; 0x04C11DB7;
                            0x04C11DB7; 0x000000AF; 0x1EDC6F41; 0xA833982B; 0x814141AB].
  Definition CRC32_Init := [0xFFFFFFFF; 0xFFFFFFFF; 0xFFFFFFFF; 0xFFFFFFFF; 0x00000000;
                            0x52325032; 0x00000000; 0xFFFFFFFF; 0xFFFFFFFF; 0x00000000].
  Definition CRC32_RefIn := [true; false; true; false; false;
                             false; false; true; true; false].
  Definition CRC32_XorOut := [0xFFFFFFFF; 0xFFFFFFFF; 0x00000000; 0x00000000; 0xFFFFFFFF;
                              0x00000000; 0x00000000; 0xFFFFFFFF; 0xFFFFFFFF; 0x00000000].
  Definition CRC32_Check := [0xCBF43926; 0xFC891918; 0x340BC6D9; 0x0376E6E7; 0x765E7680;
                             0xCF72AFE8; 0xBD0BE338; 0xE3069283; 0x87315576; 0x3010BF7F].

  Lemma CRC32_Correct:
    map (fun i => to_N (compute_crc 32 (Nnth i CRC32_Poly) (Nnth i CRC32_Init)
                       (Nnth i CRC32_XorOut) (Bnth i CRC32_RefIn) (Bnth i CRC32_RefIn) data))
      (seq 0 (length CRC32_Poly)) = CRC32_Check.
  Proof. vm_compute. reflexivity. Qed.

End CRC_CHECK.

(* Z.of_N (to_N Bits *)
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
