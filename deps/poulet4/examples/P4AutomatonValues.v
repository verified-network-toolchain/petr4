Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.AList.
Require Import Poulet4.Bitwise.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Open Scope string_scope.
Open Scope list_scope.

Section P4Automaton.

  Record p4automaton := MkP4Automaton {
    store: Type;
    states: Type;
    size: states -> nat;
    update: states -> list bool -> store -> store;
    transitions: states -> store -> states + bool;
  }.

  Definition configuration (a: p4automaton) : Type :=
    (states a + bool) * store a * list bool
  .

  Definition step
    {a: p4automaton}
    (c: configuration a)
    (b: bool)
    : configuration a
  :=
    let '(state, st, buf) := c in
    match state with
    | inl state =>
      let buf' := buf ++ b :: nil in
      if List.length buf' == size a state
      then
        let st' := update a state buf' st in
        let state' := transitions a state st' in
        (state', st', nil)
      else (inl state, st, buf')
    | inr halt =>
      (inr halt, st, buf ++ b :: nil)
    end
  .

Definition follow
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : configuration a
:=
  fold_left step input c
.

Lemma follow_cons
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  (input: list bool)
:
  follow c (b :: input) = follow (step c b) input
.
Proof.
  reflexivity.
Qed.

Definition accepted
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : Prop
:=
  fst (fst (follow c input)) = inr true
.

Definition lang_equiv
  {a1: p4automaton}
  {a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  forall input,
    accepted c1 input <->
    accepted c2 input
.

Definition bisimulation
  {a1: p4automaton}
  {a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:=
  forall c1 c2,
    R c1 c2 ->
      (fst (fst c1) = inr true <-> fst (fst c2) = inr true) /\
      forall b, R (step c1 b) (step c2 b)
.

Definition bisimilar
  {a1: p4automaton}
  {a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  exists R, bisimulation R /\ R c1 c2
.

Lemma bisimilar_implies_equiv
  {a1: p4automaton}
  {a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  bisimilar c1 c2 -> lang_equiv c1 c2
.
Proof.
  intros.
  unfold lang_equiv.
  intros; revert c1 c2 H.
  induction input; intros.
  - unfold accepted.
    simpl.
    unfold bisimilar in H.
    destruct H as [R [? ?]].
    now apply H in H0.
  - unfold accepted.
    repeat rewrite follow_cons.
    apply IHinput.
    unfold bisimilar in H.
    destruct H as [R [? ?]].
    exists R.
    apply H in H0.
    easy.
Qed.

Lemma lang_equiv_is_bisimulation
  {a1: p4automaton}
  {a2: p4automaton}
:
  @bisimulation a1 a2 lang_equiv
.
Proof.
  unfold bisimulation; intros.
  split.
  - apply (H nil).
  - intros.
    unfold lang_equiv.
    intros.
    unfold accepted.
    repeat rewrite <- follow_cons.
    apply H.
Qed.

Lemma equiv_implies_bisimilar
  {a1: p4automaton}
  {a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  lang_equiv c1 c2 -> bisimilar c1 c2
.
Proof.
  intros.
  exists lang_equiv.
  split; try easy.
  apply lang_equiv_is_bisimulation.
Qed.

Theorem bisimilar_iff_lang_equiv
  {a1: p4automaton}
  {a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  lang_equiv c1 c2 <-> bisimilar c1 c2
.
Proof.
  split.
  - apply equiv_implies_bisimilar.
  - apply bisimilar_implies_equiv.
Qed.

End P4Automaton.

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

  Scheme Equality for states.

  Instance states_eq_dec_inst : EqDec states eq := {
    equiv_dec := states_eq_dec;
  }.

  Definition size' (s: states) := 
    match s with 
    | one => 2
    | zero => 3
    end.
  

  Definition simple_auto : p4automaton := {| 
    size := size';
    update := fun s bs (v: unit) => v ;
    transitions := fun s v => 
      match s with 
      | one => inl zero
      | zero => inr true
      end
  |}.

  Definition simple_config : configuration simple_auto := 
    (inl one, tt, nil).
End SimpleParser.
  

Module BabyIPv1.
  Inductive states :=
  | start
  | parse_udp
  | parse_tcp
  .

  Scheme Equality for states.

  Instance states_eq_dec_inst : EqDec states eq := {
    equiv_dec := states_eq_dec;
  }.

  Definition size' (s: states) : nat :=
    match s with
    | start => 20
    | parse_udp => 20
    | parse_tcp => 28
    end
  .
  Definition values := @ValueBase Info.

  (*
  Definition ip_hdr := HAList.t (
    ("src", values) ::
    ("dst", values) ::
    ("proto", values) ::
    nil
  ).

  Definition udp_hdr := HAList.t (
    ("sport", values) ::
    ("dport", values) ::
    ("flags", values) ::
    nil
  ).

  Definition tcp_hdr := HAList.t (
    ("sport", values) ::
    ("dport", values) ::
    ("flags", values) ::
    ("seq", values) ::
    nil
  ).

  Definition store' := HAList.t (
    ("ip", ip_hdr) ::
    ("udp", udp_hdr) ::
    ("tcp", tcp_hdr) ::
    nil
  ).
  *)

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
        | Some (ValBaseBit 4 1) => inl parse_udp
        | Some (ValBaseBit 4 0) => inl parse_tcp
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_udp => inr true
    | parse_tcp => inr true
    end
  .

  Definition v1_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.

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

    - simpl; split; trivial.
    - exfalso. inversion H.

  Qed.


End BabyIPv1.

Module BabyIPv2.
  Inductive states :=
  | start
  | parse_tcp
  .

  Scheme Equality for states.

  Instance states_eq_dec_inst : EqDec states eq := {
    equiv_dec := states_eq_dec;
  }.

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
        | Some (ValBaseBit 4 1) => inr true
        | Some (ValBaseBit 4 0) => inl parse_tcp
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_tcp => inr true
    end
  .

  Definition v2_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.

End BabyIPv2.

(* Inductive candidate:
  configuration BabyIPv1.v1_parser ->
  configuration BabyIPv2.v2_parser ->
  Prop
:=
| BisimulationStart:
    forall st1 st2 buf,
      List.length buf < 20 ->
      candidate
        (inl BabyIPv1.start, st1, buf)
        (inl BabyIPv2.start, st2, buf)

| BisimulationEnd:
    forall st1 st2 buf1 buf2 b,
      candidate
        (inr b, st1, buf1)
        (inr b, st2, buf2)

| BisimulationTCPVersusIP:
    forall st1 buf1 st2 buf2,
      st1.(BabyIPv1.store_ip_hdr).(BabyIPv1.ip_proto) = 0 ->
      slice 16 20 buf2 = false :: false :: false :: false :: nil ->
      List.length buf2 = 20 ->
      List.length buf1 < 20 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2 ++ buf1)

| BisimulationTCPVersusTCP:
    forall st1 buf1 st2 buf2,
      List.length buf1 = 20 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1 ++ buf2)
        (inl BabyIPv2.parse_tcp, st2, buf2)

| BisimulationUDPVersusIP:
    forall st1 buf1 st2 buf2,
      st1.(BabyIPv1.store_ip_hdr).(BabyIPv1.ip_proto) = 1 ->
      slice 16 20 buf2 = true :: false :: false :: false :: nil ->
      List.length buf2 = 20 ->
      List.length buf1 < 20 ->
      candidate
        (inl BabyIPv1.parse_udp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2 ++ buf1)

| BisimulationFalseVersusStart:
    forall st1 buf1 st2 buf2,
      List.length buf2 = 20 ->
      skipn 16 buf2 <> true :: false :: false :: false :: nil ->
      skipn 16 buf2 <> false :: false :: false :: false :: nil ->
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
    to_nat (b :: l) / 2 = to_nat l
.
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

Require Import Coq.Init.Nat.

Lemma to_nat_roundtrip n s:
  n < pow 2 s ->
  to_nat (to_bits s n) = n
.
Admitted.

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

Ltac wrangle_length :=
  repeat match goal with
  | H: _ ++ _ = _ |- _ =>
    apply (f_equal (@Datatypes.length bool)) in H
  | H: _ = _ ++ _ |- _ =>
    apply (f_equal (@Datatypes.length bool)) in H
  | H: context [ Datatypes.length (_ ++ _) ] |- _ =>
    rewrite app_length in H
  | |- context [ Datatypes.length (_ ++ _) ] =>
    rewrite app_length
  | H: context [ Datatypes.length (skipn _ _) ] |- _ =>
    rewrite skipn_length in H
  | |- context [ Datatypes.length (skipn _ _) ] =>
    rewrite skipn_length
  | H: context [ Datatypes.length (slice _ _ _) ] |- _ =>
    apply length_slice in H
  | |- context [ Datatypes.length (slice _ _ _) ] =>
    apply length_slice
  end;
  simpl Datatypes.length in *;
  try lia
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
    end;

    (* Try to discharge contradictory or easy goals. *)
    try constructor;
    try wrangle_length;
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

Ltac smtize :=
  simpl;
  try wrangle_length;
  repeat (
    unfold "===", complement, slice in *;
    simpl "-" in *;
    match goal with
    | H: context [ Datatypes.length (firstn _ _) ] |- _ =>
      rewrite firstn_length' in H by wrangle_length
    | |- context [ Datatypes.length (firstn _ _) ] =>
      rewrite firstn_length' by wrangle_length
    | H: context [ Datatypes.length (skipn _ _) ] |- _ =>
      rewrite skipn_length in H by wrangle_length
    | |- context [ Datatypes.length (skipn _ _) ] =>
      rewrite skipn_length by wrangle_length
    | H: context [ nth _ (skipn _ _) _ ] |- _ =>
      rewrite nth_skipn in H;
      simpl "+" in H
    | |- context [ nth ?n (skipn ?i ?l) ?d ] =>
      rewrite nth_skipn;
      simpl "+"
    | H: to_nat ?l = _ |- _ =>
      apply (f_equal (to_bits (Datatypes.length l))) in H;
      rewrite to_bits_roundtrip in H by reflexivity
    | |- to_nat ?l = ?v =>
      symmetry;
      rewrite <- to_nat_roundtrip with (n := v) (s := Datatypes.length l) at 1;
      [symmetry; f_equal|]
    | H: firstn (S _) _ = _ :: _ |- _ =>
      repeat (
        apply firstn_cons in H;
        destruct H as [? [? H]]
      )
    | |- firstn (S _) _ = _ :: _  =>
      repeat (
        apply firstn_cons;
        repeat split;
        (assumption || lia || wrangle_length)
      )
    | H: skipn _ _ = _ :: _ |- _ =>
      repeat (
        apply skipn_cons in H;
        destruct H as [? [? H]]
      )
    | |- skipn _ _ = _ :: _ =>
      repeat (
        apply skipn_cons;
        repeat split;
        (assumption || lia || wrangle_length)
      )
    | |- skipn _ _ = nil =>
      apply skipn_all2; wrangle_length
    | H: context [ to_bits _ _ ] |- _ =>
      simpl to_bits in H
    | |- context [ to_bits _ _ ] =>
      simpl to_bits
    end
  );
  try (congruence || (simpl; lia));
  repeat match goal with
  | H: nth ?p ?l ?v1 = ?v1, H1: nth ?p ?l ?v2 = ?v2 |- _ =>
    rewrite nth_indep with (d' := v2) in H by wrangle_length;
    congruence
  | H: context [ nth _ (_ ++ _) _ ] |- _ =>
    rewrite app_nth1 in H by wrangle_length
  | |- context [nth _ (_ ++ _) _] =>
    rewrite app_nth1 by wrangle_length
  end;
  try congruence
.

Lemma candidate_is_bisimulation:
  bisimulation candidate
.
Proof.
  Opaque skipn.
  unfold bisimulation; intros.
  induction H; (split; [try easy|]); intros.
  2: { split; intros; inversion H; easy. }
  - cleanup_step.
    destruct (equiv_dec _ 1); [|destruct (equiv_dec _ 0)].
    + rewrite <- app_nil_r with (l := buf ++ b :: nil) at 1.
      apply BisimulationUDPVersusIP; smtize.
    + rewrite  <- app_nil_r with (l := buf ++ b :: nil) at 1.
      apply BisimulationTCPVersusIP; smtize.
    + rewrite <- app_nil_r with (l := buf ++ b :: nil) at 1.
      apply BisimulationFalseVersusStart.
      * wrangle_length.
      * contrapositive c0.
        smtize.
      * contrapositive c1.
        smtize.
  - simpl.
    apply BisimulationEnd.
  - cleanup_step.
    + destruct (equiv_dec _ 1); [|destruct (equiv_dec _ 0)].
      * smtize.
      * rewrite <- app_nil_r with (l := buf1 ++ b :: nil) at 1.
        apply BisimulationTCPVersusTCP.
        wrangle_length.
      * contradiction c1.
        smtize.
    + rewrite <- app_assoc.
      apply BisimulationTCPVersusIP; try assumption.
      wrangle_length.
  - cleanup_step.
    rewrite <- app_assoc.
    now apply BisimulationTCPVersusTCP.
  - cleanup_step.
    + destruct (equiv_dec _ 1); [|destruct (equiv_dec _ 0)].
      * constructor.
      * smtize.
      * contradiction c.
        smtize.
    + rewrite <- app_assoc.
      apply BisimulationUDPVersusIP; try assumption.
      wrangle_length.
  - cleanup_step.
    + destruct (equiv_dec (to_nat _) _); [|destruct (equiv_dec (to_nat _) _)].
      * contradiction H0.
        smtize.
      * contradiction H1.
        smtize.
      * constructor.
    + rewrite <- app_assoc.
      apply BisimulationFalseVersusStart; congruence.
  Transparent skipn.
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
  exists candidate.
  split.
  - apply candidate_is_bisimulation.
  - constructor.
    simpl Datatypes.length.
    lia.
Qed. *)
