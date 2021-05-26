Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.AList.
Require Import Poulet4.Bitwise.
Require Import Poulet4.P4automata.P4automaton.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Open Scope string_scope.
Open Scope list_scope.

Definition to_val (w: nat) (bs: list bool) : @ValueBase Info :=
  let v := to_nat bs in
  ValBaseBit w (Z.of_nat v).

Definition mkField (s: string) : P4String.t Info :=
  {| P4String.tags := NoInfo ; str := s |}.

Definition mkEntry (s: string) (v: @ValueBase Info): P4String.t Info * ValueBase :=
  (mkField s, v).

Definition slice {A} to from (l: list A) := firstn (from - to) (skipn to l).

Instance StrEqDec : EqDec string eq := {
  equiv_dec := string_dec;
}.

(* first we parse a simple language: 11000 *)
Module SimpleParser.
  Inductive states :=
  | one
  | zero.

  Definition size' (s: states) :=
    match s with
    | one => 2
    | zero => 3
    end.


  Program Definition simple_auto : p4automaton := {|
    size := size';
    update := fun s bs (v: unit) => v ;
    transitions := fun s v =>
      match s with
      | one => inl zero
      | zero => inr true
      end
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

  Definition simple_config : configuration simple_auto :=
    (inl one, tt, nil).
End SimpleParser.


Module BabyIPv1.
  Inductive states :=
  | start
  | parse_udp
  | parse_tcp
  .

  Definition size' (s: states) : nat :=
    match s with
    | start => 20
    | parse_udp => 20
    | parse_tcp => 28
    end
  .
  Definition values := @ValueBase Info.

  Record store' := MkStore {
    store_ip_hdr: values;
    store_u_or_t_hdr: values + values;
  }.

  Instance etaStore : Settable _ := settable! MkStore <store_ip_hdr; store_u_or_t_hdr >.

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        mkEntry "src" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dst" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "proto" (to_val 4 (slice 16 20 bs)) :: nil in
      st <| store_ip_hdr := ValBaseHeader fields true |>
    | parse_udp =>
      let fields :=
        mkEntry "sport" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dport" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "flags" (to_val 4 (slice 16 20 bs)) :: nil in
      st <| store_u_or_t_hdr := inl (ValBaseHeader fields true) |>
    | parse_tcp =>
      let fields :=
        mkEntry "sport" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dport" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "flags" (to_val 4 (slice 16 20 bs)) ::
        mkEntry "seq" (to_val 8 (slice 20 28 bs)) :: nil in
      st <| store_u_or_t_hdr := inr (ValBaseHeader fields true) |>
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      match st.(store_ip_hdr) with
      | ValBaseHeader fields true =>
        match AList.get fields (mkField "proto") with
        | Some (ValBaseBit 4 z) =>
          if z == Z.of_nat 1 then inl parse_udp
          else if z == Z.of_nat 0 then inl parse_tcp
          else inr false
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_udp => inr true
    | parse_tcp => inr true
    end
  .

  Program Definition v1_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

  Record SwitchState := mkSwitchState {
    egress_spec : @ValueBase Info;
  }.

  Instance etaSwitchState : Settable _ := settable! mkSwitchState <egress_spec >.

  Definition v1_control (s: store') (state: SwitchState) : SwitchState :=
    match s.(store_u_or_t_hdr) with
    | inl (ValBaseHeader _ true) => state <| egress_spec := ValBaseBit 8 0 |>
    | _ => state <| egress_spec := ValBaseBit 8 1 |>
    end.

  Definition init_config: configuration v1_parser :=
    let blank_store := {| store_ip_hdr := ValBaseHeader nil false; store_u_or_t_hdr := inl (ValBaseHeader nil false) |} in
    (inl start, blank_store, nil).

  Definition v1_program (pkt: list bool) (state: SwitchState) : SwitchState :=
    let '(_, final_store, _) := follow init_config pkt in
    v1_control final_store state.

  Definition repr_tcp (bs: list bool) : Prop :=
    List.length bs = 48 /\ (to_nat (slice 16 20 bs) = 1).

  Lemma baby_ip_corr :
    forall pkt st st',
      repr_tcp pkt ->
      st' = v1_program pkt st ->
        accepted init_config pkt /\
        st'.(egress_spec) = ValBaseBit 8 0.
  Proof.
    intros.

    unfold repr_tcp in H.
    destruct H.
    rewrite H0.
    unfold v1_program.
    unfold egress_spec, accepted.
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    unfold slice in *.
    simpl in H1 |- *.
    rewrite H1.
    simpl.
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    unfold slice.
    simpl.
    do 8 (destruct pkt; [exfalso; inversion H| simpl]).
    destruct pkt.

    - simpl; split; unfold accepting; trivial.
    - exfalso. inversion H.

  Qed.
End BabyIPv1.

Module BabyIPv2.
  Inductive states :=
  | start
  | parse_tcp
  .

  Definition size' (s: states) : nat :=
    match s with
    | start => 40
    | parse_tcp => 8
    end
  .

  Definition values := @ValueBase Info.


  Record store' := MkStore {
    store_combined_hdr: values;
    store_optional_hdr: values;
  }.

  Instance etaStore : Settable _ := settable! MkStore <store_combined_hdr; store_optional_hdr>.

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        mkEntry "src" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dst" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "proto" (to_val 4 (slice 16 20 bs)) ::
        mkEntry "sport" (to_val 8 (slice 20 28 bs)) ::
        mkEntry "dport" (to_val 8 (slice 28 36 bs)) ::
        mkEntry "flags" (to_val 4 (slice 36 40 bs)) :: nil in
        st <| store_combined_hdr := ValBaseHeader fields true |>
    | parse_tcp =>
      let fields :=
        mkEntry "seq" (to_val 8 (slice 0 8 bs)) :: nil in
        st <| store_optional_hdr := ValBaseHeader fields true |>
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      match st.(store_combined_hdr) with
      | ValBaseHeader fields true =>
        match AList.get fields (mkField "proto") with
        | Some (ValBaseBit 4 z) =>
          if z == Z.of_nat 1 then inr true
          else if z == Z.of_nat 0 then inl parse_tcp
          else inr false
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_tcp => inr true
    end
  .

  Program Definition v2_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

End BabyIPv2.

Inductive candidate:
  configuration BabyIPv1.v1_parser ->
  configuration BabyIPv2.v2_parser ->
  Prop
:=
| BisimulationStart:
    forall st1 st2,
      candidate
        (inl BabyIPv1.start, st1, nil)
        (inl BabyIPv2.start, st2, nil)

| BisimulationEnd:
    forall st1 st2 buf1 buf2 h,
      candidate
        (inr h, st1, buf1)
        (inr h, st2, buf2)

| BisimulationTCPVersusIP:
    forall st1 ip_hdr st2 buf,
      st1.(BabyIPv1.store_ip_hdr) = ValBaseHeader ip_hdr true ->
      AList.get ip_hdr (mkField "proto") = Some (ValBaseBit 4 0) ->
      to_nat (slice 16 20 buf) = 0 ->
      List.length buf = 20 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, nil)
        (inl BabyIPv2.start, st2, buf)

| BisimulationTCPVersusTCP:
    forall st1 st2 buf,
      List.length buf = 20 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf)
        (inl BabyIPv2.parse_tcp, st2, nil)

| BisimulationUDPVersusIP:
    forall st1 ip_hdr st2 buf,
      st1.(BabyIPv1.store_ip_hdr) = ValBaseHeader ip_hdr true ->
      AList.get ip_hdr (mkField "proto") = Some (ValBaseBit 4 1) ->
      to_nat (slice 16 20 buf) = 1 ->
      List.length buf = 20 ->
      candidate
        (inl BabyIPv1.parse_udp, st1, nil)
        (inl BabyIPv2.start, st2, buf)

| BisimulationFalseVersusStart:
    forall st1 buf1 st2 buf2,
      List.length buf2 = 20 ->
      to_nat (slice 16 20 buf2) <> 1 ->
      to_nat (slice 16 20 buf2) <> 0 ->
      candidate
        (inr false, st1, buf1)
        (inl BabyIPv2.start, st2, buf2 ++ buf1)
.

Fixpoint to_bits (s n: nat) :=
  match s with
  | 0 => nil
  | S s' =>
    if n mod 2 == 0 then
      false :: to_bits s' (n / 2)
    else
      true :: to_bits s' (n / 2)
  end
.

Lemma to_nat_div:
  forall b l,
    to_nat (b :: l) / 2 = to_nat l.
Proof.
Admitted.

Lemma to_nat_mod:
  forall b l,
    to_nat (b :: l) mod 2 = 0 <-> false = b
.
Admitted.

Lemma to_bits_roundtrip n:
  forall l,
    Datatypes.length l = n ->
    to_bits n (to_nat l) = l
.
Proof.
  induction n; intros.
  - simpl in *.
    symmetry.
    now apply length_zero_iff_nil.
  - unfold to_bits.
    fold to_bits.
    destruct l; [simpl in H;discriminate|].
    rewrite to_nat_div.
    rewrite IHn.
    destruct (equiv_dec _ _).
    + f_equal.
      eapply to_nat_mod.
      exact e.
    + f_equal.
      symmetry.
      apply Bool.not_false_is_true.
      contradict c.
      intro.
      apply H0.
      unfold Equivalence.equiv.
      apply to_nat_mod.
      congruence.
    + simpl in H.
      congruence.
Qed.

Lemma to_nat_versus_to_bits l n:
  to_nat l = n ->
  l = to_bits (Datatypes.length l) n
.
Proof.
  intros.
  apply (f_equal (to_bits (Datatypes.length l))) in H.
  now rewrite to_bits_roundtrip in H by reflexivity.
Qed.

Require Import Coq.Init.Nat.

Lemma to_nat_roundtrip n s:
  n < pow 2 s ->
  to_nat (to_bits s n) = n
.
Admitted.

Lemma to_bits_versus_to_nat n s l:
  l = to_bits s n ->
  n < pow 2 s ->
  to_nat l = n
.
Proof.
  intros.
  rewrite H.
  rewrite to_nat_roundtrip; easy.
Qed.

Lemma length_slice {X: Type}:
  forall i j (l: list X),
    j <= Datatypes.length l ->
    Datatypes.length (slice i j l) = j - i
.
Proof.
  intros.
  unfold slice.
  rewrite firstn_length.
  rewrite min_l.
  reflexivity.
  rewrite skipn_length.
  lia.
Qed.

Lemma firstn_length' {X: Type}:
  forall n (l: list X),
    n <= Datatypes.length l ->
    Datatypes.length (firstn n l) = n
.
Proof.
  induction n; intros.
  - simpl.
    reflexivity.
  - simpl.
    destruct l; try (simpl in *; lia).
    simpl.
    rewrite IHn; try easy.
    simpl in H.
    lia.
Qed.

Ltac simpl_length :=
  repeat (lia || match goal with
  | H: context [ Datatypes.length (_ :: nil) ] |- _ =>
    simpl Datatypes.length in H
  | |- context [ Datatypes.length (_ :: nil) ] =>
    simpl Datatypes.length
  | H: context [ Datatypes.length (_ ++ _) ] |- _ =>
    rewrite app_length in H
  | |- context [ Datatypes.length (_ ++ _) ] =>
    rewrite app_length
  | H: context [ Datatypes.length (skipn _ _) ] |- _ =>
    rewrite skipn_length in H;
    simpl "-" in H
  | |- context [ Datatypes.length (skipn _ _) ] =>
    rewrite skipn_length;
    simpl "-"
  | H: context [ Datatypes.length (firstn _ _) ] |- _ =>
    rewrite firstn_length' in H;
    simpl "^" in H
  | |- context [ Datatypes.length (firstn _ _) ] =>
    rewrite firstn_length';
    simpl "^"
  end)
.

(* Possible fallback tactic we don't use right now; derives facts about
   lengths from facts about lists. Note that this gets rid of the list
   facts, so you cannot use those later on... *)
Ltac wrangle_length :=
  repeat match goal with
  | H: _ ++ _ = _ |- _ =>
    apply (f_equal (@Datatypes.length bool)) in H
  | H: _ = _ ++ _ |- _ =>
    apply symmetry in H
  end;
  simpl_length
.

Ltac cleanup_step :=
  match goal with
  | |- ?R (step (?s1, ?st1, ?buf1) ?b) (step (?s2, ?st2, ?buf2) ?b) =>
    (* Unfold the step function, exposing the four cases for full/empty buffers. *)
    unfold step;
    simpl size;

    (* Split up into four cases, depending on which buffers are full. *)
    try destruct (equiv_dec (Datatypes.length (buf1 ++ b :: nil)) _);
    try destruct (equiv_dec (Datatypes.length (buf2 ++ b :: nil)) _);

    (* Clean up the premises, getting rid of the types of equivalence that lia does not like. *)
    unfold Equivalence.equiv, complement in *;
    repeat match goal with
    | [ H: ?l = ?r -> False |- _ ] =>
      fold (not (l = r)) in H
    | H: _ /\ _ |- _ =>
      destruct H
    end;

    (* Try to discharge contradictory or easy goals. *)
    try constructor;
    repeat match goal with
    | |- _ /\ _ =>
      split
    end;
    try trivial;
    try congruence;
    try simpl_length;
    simpl
  end
.

Lemma skipn_cons {X: Type} i l (b: X) l':
  skipn i l = b :: l'
  <->
  i < Datatypes.length l /\ nth i l b = b /\ skipn (S i) l = l'
.
Proof.
  revert l l'.
  induction i; intros.
  - split; intros.
    + simpl in H.
      subst.
      repeat split.
      simpl.
      lia.
    + simpl.
      destruct H as [? [? ?]].
      destruct l; try (simpl in H; lia).
      simpl in H0.
      now subst.
  - split; intros.
    + simpl in H.
      destruct l; try discriminate.
      apply IHi in H; clear IHi.
      destruct H as [? [? ?]].
      simpl in *.
      repeat split.
      * lia.
      * assumption.
      * congruence.
    + simpl.
      destruct l; simpl in *; try lia.
      apply IHi; clear IHi.
      destruct H as [? [? ?]].
      repeat split.
      * lia.
      * assumption.
      * congruence.
Qed.

Lemma firstn_cons {X: Type} i l (b: X) l':
  firstn (S i) l = b :: l' <->
  nth 0 l b = b /\ firstn i (skipn 1 l) = l' /\ 0 < Datatypes.length l
.
Proof.
  split; intros.
  - simpl in H.
    destruct l; try discriminate.
    simpl.
    inversion H.
    repeat split; (reflexivity || lia).
  - simpl.
    destruct H as [? [? ?]].
    destruct l; simpl in *; try lia.
    f_equal; congruence.
Qed.

Lemma nth_skipn {X: Type} n i l (d: X):
  nth n (skipn i l) d = nth (i+n) l d
.
Proof.
  revert l; induction i; intros.
  - rewrite skipn_O.
    reflexivity.
  - simpl.
    destruct l.
    + simpl.
      now destruct n.
    + simpl.
      apply IHi.
Qed.

Ltac contrapositive H :=
  intro; apply H
.

Lemma to_bits_vs_pos_to_nat_true n p:
  to_bits (S n) (Pos.to_nat p~1) = true :: to_bits n (Pos.to_nat p)
.
Proof.
Admitted.

Lemma to_bits_vs_pos_to_nat_false n p:
  to_bits (S n) (Pos.to_nat p~0) = false :: to_bits n (Pos.to_nat p)
.
Proof.
Admitted.

Lemma to_bits_vs_pos_to_nat_plain p n:
  to_bits (S n) (Pos.to_nat p) = true :: repeat false n
.
Proof.
Admitted.

Ltac is_num_literal t :=
  match t with
  | 0 => idtac
  | S ?t' =>
    is_num_literal t'
  end
.

Ltac smtize :=
  try assumption;
  (* Simplify mostly header projections first. *)
  simpl;
  (* Simplify (in)equalities to props. *)
  unfold "===", complement in *;
  (* Desugar calls to slice. *)
  unfold slice in *;
  simpl "-" in *;
  (* First heavy pass: try to turn premises and goals about natural numbers
     into premises and goals about lists of booleans. *)
  repeat (
    simpl_length;
    match goal with
    | |- ValBaseHeader _ _ = ValBaseHeader _ _ =>
      f_equal
    | |- get _ (mkField _) = _ =>
      unfold get; simpl; f_equal
    | |- to_val ?s _ = ValBaseBit ?s _ =>
      unfold to_val; f_equal
    | H: Z.of_nat _ = Z.of_nat _ |- _ =>
      apply Nat2Z.inj in H
    | H: Z.of_nat _ = _ |- _ =>
      apply (f_equal Z.abs_nat) in H;
      simpl in H;
      rewrite Zabs2Nat.id in H
    | |- Z.of_nat _ = Z.of_nat _ =>
      f_equal
    | H: to_nat _ = _ |- _ =>
      apply to_nat_versus_to_bits in H
    | |- to_nat ?l = _ =>
      apply to_bits_versus_to_nat with (s := Datatypes.length l)
    | H: context [ to_bits (S ?n) (Pos.to_nat ?p~1) ] |- _ =>
      rewrite to_bits_vs_pos_to_nat_true in H
    | H: context [ to_bits (S ?n) (Pos.to_nat ?p~0) ] |- _ =>
      rewrite to_bits_vs_pos_to_nat_false in H
    | H: context [ to_bits (S ?n) (Pos.to_nat ?p) ] |- _ =>
      rewrite to_bits_vs_pos_to_nat_plain in H;
      simpl repeat in H
    | H: context [ to_bits ?s ?n ] |- _ =>
      is_num_literal s;
      is_num_literal n;
      simpl to_bits in H
    | |- context [ to_bits ?s ?n ] =>
      is_num_literal s;
      is_num_literal n;
      simpl to_bits
    end
  );
  try congruence;
  (* Second heavy pass: deconstruct goals and premises about parts of the
     lists of booleans created above into goals and premises about specific
     bits within those lists. *)
  repeat (
    match goal with
    | H: firstn (S _) _ = _ :: _ |- _ =>
      apply firstn_cons in H;
      destruct H as [? [? H]]
    | |- firstn (S _) _ = _ :: _  =>
      apply firstn_cons;
      repeat split; simpl_length
    | H: skipn _ _ = _ :: _ |- _ =>
      apply skipn_cons in H;
      destruct H as [? [? H]]
    | |- skipn _ _ = _ :: _ =>
      apply skipn_cons;
      repeat split; simpl_length
    | |- skipn _ _ = nil =>
      apply skipn_all2
    | H: context [ nth _ (skipn _ _) _ ] |- _ =>
      rewrite nth_skipn in H;
      simpl "+" in H
    | |- context [ nth _ (skipn _ _) _ ] =>
      rewrite nth_skipn;
      simpl "+"
    end
  );
  try congruence;
  (* Final heavy pass: try to discover contradictions about specific bits
     inside the premises, i.e., a pair of assertions saying one bit is true
     while another is false. Also try to guess the position of bits inside
     composite lists in order to expose more candidate matches. *)
  repeat match goal with
  | H: nth ?p ?l false = false, H1: nth ?p ?l true = true |- _ =>
    rewrite nth_indep with (d' := true) in H by simpl_length;
    congruence
  | H: context [ nth _ (_ ++ _) _ ] |- _ =>
    rewrite app_nth1 in H by simpl_length
  | |- context [nth _ (_ ++ _) _] =>
    rewrite app_nth1 by simpl_length
  end;
  try congruence;
  (* Hail Mary: try and derive a contradiction with some negative premise. *)
  unfold not in *;
  match goal with
  | H: _ -> False |- _ =>
    contradiction H;
    clear H;
    smtize
  | _ => idtac "foo"
  end
.

Lemma done_stuck:
  forall buf h st1 st2 buf1 buf2,
    candidate (follow (inr h, st1, buf1) buf) (follow (inr h, st2, buf2) buf)
.
Proof.
  induction buf; intros.
  - repeat rewrite follow_nil.
    constructor.
  - repeat rewrite follow_cons.
    apply IHbuf.
Qed.

Lemma candidate_is_bisimulation:
  bisimulation_with_leaps candidate
.
Proof.
  Opaque skipn.
  Opaque firstn.
  Opaque Z.of_nat.
  unfold bisimulation_with_leaps; intros.
  induction H; (split; [try easy|]); intros.
  2: { split; intros; inversion H;  easy. }
  - simpl min in H.
    rewrite (@follow_buffer BabyIPv2.v2_parser); [|smtize].
    rewrite (@follow_exact BabyIPv1.v1_parser); [|smtize|smtize].
    simpl; repeat destruct (equiv_dec _ _).
    + econstructor; smtize.
    + econstructor; smtize.
    + rewrite <- app_nil_r with (l := buf) at 1.
      constructor; smtize.
  - apply done_stuck.
  - simpl min_step in H3.
    rewrite H2 in H3.
    simpl in H3.
    rewrite (@follow_exact BabyIPv2.v2_parser); [|smtize|smtize].
    rewrite (@follow_buffer BabyIPv1.v1_parser); [|smtize].
    simpl; repeat destruct (equiv_dec _ _); try constructor; smtize.
  - simpl min_step in H0.
    rewrite H in H0.
    simpl in H0.
    rewrite (@follow_exact BabyIPv1.v1_parser); [|smtize|smtize].
    rewrite (@follow_exact BabyIPv2.v2_parser); [|smtize|smtize].
    simpl.
    constructor.
  - simpl min_step in H3.
    rewrite H2 in H3.
    simpl in H3.
    rewrite (@follow_exact BabyIPv1.v1_parser); [|smtize|smtize].
    rewrite (@follow_exact BabyIPv2.v2_parser); [|smtize|smtize].
    simpl.
    repeat destruct (equiv_dec _ _); try constructor; smtize.
  - clear H2.
    revert st1 buf1 st2 buf2 H H0 H1; induction buf; intros.
    + repeat rewrite follow_nil.
      now constructor.
    + repeat rewrite follow_cons.
      unfold step; simpl.
      repeat destruct (equiv_dec _ _).
      * smtize.
      * smtize.
      * apply done_stuck.
      * rewrite <- app_assoc.
        apply IHbuf; smtize.
Qed.

Theorem babyip_equiv
  st1 st2
:
  @lang_equiv BabyIPv1.v1_parser
              BabyIPv2.v2_parser
              (inl BabyIPv1.start, st1, nil)
              (inl BabyIPv2.start, st2, nil)
.
Proof.
  apply bisimilar_iff_lang_equiv.
  apply bisimilar_iff_bisimilar_with_leaps.
  exists candidate.
  split.
  - constructor.
  - apply candidate_is_bisimulation.
Qed.

(* TODO: The following is a more structured version of the ad-hoc candidate
   bisimulation built above. Can we make the proof automation nicer if we
   know that every clause is structed this way?

   The main hurdle seems to be in the folding/unfolding of the
   build_bisimulation helper. The constructor tactic does not apply
   unless we have our goal in that form. *)

Definition build_bisimulation
  {a1 a2}
  (store_relation_l : store a1 -> Prop)
  (store_relation_r : store a2 -> Prop)
  (st1: states a1 + bool)
  (st2: states a2 + bool)
  (buf_relation : list bool -> list bool -> Prop)
  (cand : configuration a1 -> configuration a2 -> Prop)
  : Prop :=
  forall sig1 buf1 sig2 buf2,
    store_relation_l sig1 ->
    store_relation_r sig2 ->
    buf_relation buf1 buf2 ->
    cand (st1, sig1, buf1) (st2, sig2, buf2).

Definition store_top {a} : store a -> Prop := fun _ => True.

Inductive candidate':
  configuration BabyIPv1.v1_parser ->
  configuration BabyIPv2.v2_parser ->
  Prop
:=
| BisimulationStart':
    build_bisimulation
      (a1 := BabyIPv1.v1_parser)
      (a2 := BabyIPv2.v2_parser)
      store_top
      store_top
      (inl BabyIPv1.start)
      (inl BabyIPv2.start)
      (fun buf buf' => List.length buf < 20 /\ buf = buf')
      candidate'

| BisimulationEnd':
  forall b,
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    store_top
    store_top
    (inr b)
    (inr b)
    (fun _ _ => True)
    candidate'

| BisimulationTCPVersusIP':
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    (fun s =>
      forall ip_hdr,
      s.(BabyIPv1.store_ip_hdr) = ValBaseHeader ip_hdr true ->
      AList.get ip_hdr (mkField "proto") = Some (ValBaseBit 4 0)
    )
    store_top
    (inl BabyIPv1.parse_tcp)
    (inl BabyIPv2.start)
    (fun buf1 buf2 =>
      to_nat (slice 16 20 buf2) = 0 /\
      List.length buf2 = 20 /\
      List.length buf1 < 20
    )
    candidate'

| BisimulationTCPVersusTCP':
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    store_top
    store_top
    (inl BabyIPv1.parse_tcp)
    (inl BabyIPv2.parse_tcp)
    (fun buf1 buf2 =>
      exists pref,
      List.length pref = 20 /\
      buf1 = pref ++ buf2
    )
    candidate'

| BisimulationUDPVersusIP':
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    (fun s =>
      forall ip_hdr,
      s.(BabyIPv1.store_ip_hdr) = ValBaseHeader ip_hdr true ->
      AList.get ip_hdr (mkField "proto") = Some (ValBaseBit 4 1)
    )
    store_top
    (inl BabyIPv1.parse_udp)
    (inl BabyIPv2.start)
    (fun buf1 buf2 =>
      exists pref,
      to_nat (slice 16 20 pref) = 1 /\
      List.length pref = 20 /\
      List.length buf1 < 20 /\
      buf2 = pref ++ buf1
    )
    candidate'

| BisimulationFalseVersusStart':
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    store_top
    store_top
    (inr false)
    (inl BabyIPv2.start)
    (fun buf1 buf2 =>
      exists pref,
      buf2 = pref ++ buf1 /\
      List.length pref = 20 /\
      to_nat (slice 16 20 pref) <> 1 /\
      to_nat (slice 16 20 pref) <> 0
    )
    candidate'
.
