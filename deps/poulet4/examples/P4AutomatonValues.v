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

Definition accepting
  {a: p4automaton}
  (c: configuration a)
  : Prop
:=
  fst (fst c) = inr true
.

Definition accepted
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : Prop
:=
  accepting (follow c input)
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
      (accepting c1 <-> accepting c2) /\
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

    - simpl; split; unfold accepting; trivial.
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

Inductive candidate:
  configuration BabyIPv1.v1_parser ->
  configuration BabyIPv2.v2_parser ->
  Prop
:=
| BisimulationStart:
    build_bisimulation
      (a1 := BabyIPv1.v1_parser)
      (a2 := BabyIPv2.v2_parser)
      store_top
      store_top
      (inl BabyIPv1.start)
      (inl BabyIPv2.start)
      (fun buf buf' => List.length buf < 20 /\ buf = buf')
      candidate


| BisimulationEnd:
  forall b,
  build_bisimulation
    (a1 := BabyIPv1.v1_parser)
    (a2 := BabyIPv2.v2_parser)
    store_top
    store_top
    (inr b)
    (inr b)
    (fun _ _ => True)
    candidate

| BisimulationTCPVersusIP:
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
    candidate

| BisimulationTCPVersusTCP:
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
    candidate

| BisimulationUDPVersusIP:
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
    candidate

| BisimulationFalseVersusStart:
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
    candidate
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
   lengths from facts about lists. Note that this gets rids of the list
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
    unfold store_top;
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
    | H: Z.of_nat _ = _ |- _ =>
      apply (f_equal Z.abs_nat) in H;
      simpl in H;
      rewrite Zabs2Nat.id in H
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
  try congruence
.

Lemma candidate_is_bisimulation:
  bisimulation candidate
.
(* Proof.
  Opaque skipn.
  Opaque firstn.
  unfold bisimulation; intros.
  induction H; (split; [try easy|]); intros.
  2: { split; intros; inversion H2; easy. }
  - cleanup_step.
    destruct (Z.of_nat _) eqn:?; [|destruct p|];
    rewrite  <- app_nil_r with (l := buf ++ b :: nil) at 1;
    econstructor;
    smtize.
  - cleanup_step.
  - cleanup_step.
    + destruct (Z.of_nat _) eqn:?; [|destruct p eqn:?|].
      * rewrite <- app_nil_r with (l := buf1 ++ b :: nil) at 1.
        apply BisimulationTCPVersusTCP; smtize.
      * smtize.
      * smtize.
      * smtize.
      * smtize.
    + rewrite <- app_assoc.
      apply BisimulationTCPVersusIP with (ip_hdr := ip_hdr); smtize.
  - cleanup_step.
    rewrite <- app_assoc.
    now apply BisimulationTCPVersusTCP.
  - cleanup_step.
    + destruct (Z.of_nat _) eqn:?; [|destruct p eqn:?|].
      * smtize.
      * smtize.
      * smtize.
      * constructor.
      * smtize.
    + rewrite <- app_assoc.
      apply BisimulationUDPVersusIP with (ip_hdr := ip_hdr); smtize.
  - cleanup_step.
    + destruct (Z.of_nat _) eqn:?; [|destruct p eqn:?|].
      * contradiction H1; smtize.
      * constructor.
      * constructor.
      * contradiction H0; smtize.
      * constructor.
    + rewrite <- app_assoc.
      apply BisimulationFalseVersusStart; assumption.
  Transparent skipn.
  Transparent firstn.
Qed. *)
Admitted.

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
  - constructor; compute; trivial.
    split.
    + lia.
    + trivial.
Qed.

Definition chunked_relation
  (a1 a2: p4automaton)
:=
  list (
    configuration a1 ->
    configuration a2 ->
    Prop
  )
.

Definition buffer_appended
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
  : Prop
:=
  let '(s, st, buf) := c in
  let '(s', st', buf') := c' in
  match s with
  | inl s => Datatypes.length buf + 1 < size a s
  | inr _ => True
  end ->
  buf' = buf ++ b :: nil
.

Definition buffer_filled
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
  : Prop
:=
  let '(s, st, buf) := c in
  let '(s', st', buf') := c' in
  match s with
  | inl s =>
    Datatypes.length buf + 1 = size a s /\
    buf' = nil /\
    st' = update a s (buf ++ b :: nil) st /\
    s' = transitions a s st'
  | inr _ => False
  end
.

Definition symbolic_step
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  : chunked_relation a1 a2
:=
  (* First case: neither buffer was filled. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Second case: the left buffer was filled, but the right was not. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Third case: the right buffer was filled, but the left was not. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  (* Fourth case: both buffers were filled. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  nil
.

Lemma appended_or_filled
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
:

  buffer_appended c (step c b) b \/
  buffer_filled c (step c b) b
.
Proof.
  destruct c as ((s, st), buf).
  destruct s.
  - simpl step.
    rewrite app_length.
    simpl Datatypes.length.
    destruct (equiv_dec (Datatypes.length buf + 1) (size a s)).
    + right.
      unfold buffer_filled.
      easy.
    + left.
      simpl.
      intros.
      easy.
  - left.
    simpl step.
    unfold buffer_appended.
    easy.
Qed.

Lemma symbolic_step_correct
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  (c1: configuration a1)
  (c2: configuration a2)
  (b: bool)
:
  R c1 c2 ->
  exists R',
    List.In R' (symbolic_step R) /\
    R' (step c1 b) (step c2 b)
.
Proof.
  intros.
  unfold symbolic_step.
  destruct (appended_or_filled c1 (step c1 b) b),
           (appended_or_filled c2 (step c2 b) b).
  - eexists; split.
    + apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + do 2 apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + do 3 apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
Qed.

Lemma bisimilar_deconstruct
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  (accepting c1 <-> accepting c2) ->
  (forall b, bisimilar (step c1 b) (step c2 b)) ->
  bisimilar c1 c2
.
Proof.
  intros.
  destruct (H0 true) as [Rtrue [? ?]].
  destruct (H0 false) as [Rfalse [? ?]].
  exists (fun c1' c2' =>
    Rtrue c1' c2' \/
    Rfalse c1' c2' \/
    (c1 = c1' /\ c2 = c2')
  ).
  split.
  - unfold bisimulation.
    intros.
    repeat destruct H5.
    + split.
      * now apply H1.
      * intuition (now apply H1).
    + split.
      * now apply H3.
      * intuition (now apply H3).
    + rewrite <- H6.
      split; try assumption.
      destruct b; intuition.
  - intuition.
Qed.

Definition pre_bisimulation
  {a1 a2: p4automaton}
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  (forall R c1 c2,
    List.In R expanded ->
    R c1 c2 ->
    (accepting c1 <-> accepting c2) /\
    forall b,
      exists R',
        List.In R' (front ++ expanded) /\
        R' (step c1 b) (step c2 b)) ->
  forall R c1 c2,
    (List.In R (front ++ expanded) ->
     R c1 c2 ->
     bisimilar c1 c2)
.

Lemma pre_bisimulation_intro
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:
  pre_bisimulation nil (R :: nil) ->
  (forall c1 c2, R c1 c2 -> bisimilar c1 c2)
.
Proof.
  intros.
  eapply H.
  - firstorder.
  - apply in_eq.
  - easy.
Qed.

Lemma pre_bisimulation_leaf
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
:
  pre_bisimulation checked nil
.
Proof.
  unfold pre_bisimulation.
  intros.
  rewrite app_nil_l in *.
  exists (fun c1 c2 =>
    exists R',
      List.In R' checked /\
      R' c1 c2
  ).
  split.
  - intros c1' c2' ?.
    destruct H2 as [R' [? ?]].
    specialize (H R' c1' c2').
    now apply H.
  - exists R; easy.
Qed.

Lemma pre_bisimulation_valid
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
  (checked front: chunked_relation a1 a2)
:
  (forall R c1 c2,
    List.In R checked ->
    R c1 c2 ->
    (accepting c1 <-> accepting c2) /\
    forall b,
      exists R',
        List.In R' (front ++ checked) /\
        R' (step c1 b) (step c2 b)) ->
  pre_bisimulation checked front ->
  (exists R, List.In R (front ++ checked) /\ R c1 c2) ->
  bisimilar c1 c2
.
Proof.
  intros.
  apply H0 in H.
  destruct H1 as [R [? ?]].
  now apply H with (R := R).
Qed.

Lemma pre_bisimulation_grow
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
  pre_bisimulation (R :: checked) (symbolic_step R ++ front) ->
  pre_bisimulation checked (R :: front)
.
Proof.
  intros; unfold pre_bisimulation; intros.
  eapply pre_bisimulation_valid.
  2: { exact H0. }
  - intros.
    specialize (H1 R1 c0 c3).
    destruct H4.
    + rewrite <- H4 in H5.
      clear H4.
      split.
      * now apply H.
      * intros.
        apply symbolic_step_correct with (b0 := b) in H5.
        destruct H5 as [R' [? ?]].
        exists R'.
        split; auto.
        rewrite <- app_assoc.
        now apply in_app_iff; left.
    + split.
      * now apply H1.
      * intros.
        specialize (H1 H4 H5).
        destruct H1.
        specialize (H6 b).
        destruct H6 as [R' [? ?]].
        exists R'.
        split; auto.
        rewrite <- app_assoc.
        repeat rewrite in_app_iff.
        repeat rewrite in_app_iff in H6.
        destruct H6.
        -- destruct H6.
           ++ right; right.
              rewrite H6.
              apply in_eq.
           ++ right; left; assumption.
        -- right; right.
           now apply in_cons.
  - exists R0.
    split; auto.
    repeat rewrite in_app_iff.
    repeat rewrite in_app_iff in H2.
    destruct H2.
    + destruct H2.
      * right.
        rewrite H2.
        apply in_eq.
      * left.
        right.
        assumption.
    + right.
      now apply in_cons.
Qed.

Lemma pre_bisimulation_skip
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  (forall c1 c2,
    R c1 c2 ->
    exists R',
      List.In R' checked /\
      R' c1 c2) ->
  pre_bisimulation checked front ->
  pre_bisimulation checked (R :: front)
.
Proof.
  intros; unfold pre_bisimulation; intros.
  eapply pre_bisimulation_valid.
  2: { exact H0. }
  - intros.
    specialize (H1 R1 c0 c3 H4 H5).
    split; try apply H1.
    intros.
    destruct H1.
    specialize (H6 b).
    destruct H6 as [R' [? ?]].
    rewrite <- app_comm_cons in H6.
    destruct H6.
    + rewrite <- H6 in H7.
      apply H in H7.
      destruct H7 as [R'' [? ?]].
      exists R''.
      split; auto.
      apply in_app_iff; now right.
    + exists R'.
      auto.
  - rewrite <- app_comm_cons in H2.
    destruct H2.
    + rewrite <- H2 in H3.
      clear H2.
      apply H in H3.
      destruct H3 as [R' [? ?]].
      exists R'.
      split; auto.
      apply in_app_iff; now right.
    + exists R0.
      auto.
Qed.

Require Import Poulet4.P4cub.AST.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.State.

Open Scope monad_scope.

Section parser_to_p4automaton.

  Variable tags_t : Type.

  Inductive simple_expression :=
  | SimpleExpressionHeader
  | SimpleExpressionMember (e: simple_expression) (m: string)
  .

  Inductive simple_lvalue :=
  | SimpleLvalueHeader
  | SimpleLvalueMember (e: simple_lvalue) (m: string)
  .

  Inductive state_operation :=
  | StateOperationNil
  | StateOperationExtract
      (typ: P4cub.Expr.t)
      (into: simple_lvalue)
  .

  Inductive simple_match :=
  | SimpleMatchEquals (l r: simple_expression)
  | SimpleMatchAnd (l r: simple_match)
  | SimpleMatchDontCare
  .

  Section compile.
    Variables (pkt_name hdr_name: string).

    Fixpoint compile_expression
      (expr: P4cub.Expr.e tags_t)
      : option simple_expression
    :=
      match expr with
      | P4cub.Expr.EVar _ name _ =>
        if name == hdr_name then
          Some SimpleExpressionHeader
        else
          None
      | P4cub.Expr.EExprMember name _ expr _ =>
        let* child := compile_expression expr in
        Some (SimpleExpressionMember child name)
      | _ =>
        None
      end
    .

    Fixpoint compile_lvalue
      (expr: P4cub.Expr.e tags_t)
      : option simple_lvalue
    :=
      match expr with
      | P4cub.Expr.EVar _ name _ =>
        if name == hdr_name then
          Some SimpleLvalueHeader
        else
          None
      | P4cub.Expr.EExprMember name _ expr _ =>
        let* child := compile_lvalue expr in
        Some (SimpleLvalueMember child name)
      | _ =>
        None
      end
    .

    Fixpoint compile_statements
      (stmt: P4cub.Stmt.s tags_t)
      : option (list state_operation)
    :=
      match stmt with
      | P4cub.Stmt.SSkip _ =>
        Some nil
      | P4cub.Stmt.SSeq s1 s2 _ =>
        let* f1 := compile_statements s1 in
        let* f2 := compile_statements s2 in
        Some (f1 ++ f2)
      | P4cub.Stmt.SExternMethodCall extern func args _ =>
        if extern == pkt_name then
          if func == "extract" then
            match args with
            | P4cub.Arrow ((_, P4cub.PAOut (t, e)) :: nil) _ =>
              let* into := compile_lvalue e in
              Some (StateOperationExtract t into :: nil)
            | _=> None
            end
          else
            None
        else
          None
      | _ => None
      end
    .

    Fixpoint compile_updates
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (list (string * list state_operation))
    :=
      match states with
      | nil =>
        Some nil
      | state :: states' =>
        let '(name, P4cub.Parser.ParserState.State stmt _) := state in
        let* tail := compile_updates states' in
        let* head := compile_statements stmt in
        Some ((name, head) :: tail)
      end
    .

    Section NotationSection.
    Import P4cub.P4cubNotations.

    Fixpoint compile_transition
      (trans: P4cub.Parser.ParserState.e tags_t)
      : option (list (simple_match * (string + bool)))
    :=
      match trans with
      | p{ goto start @ _ }p => None (* TODO: Implement this. *)
      | p{ goto accept @ _ }p =>
        Some ((SimpleMatchDontCare, inr true) :: nil)
      | p{ goto reject @ _ }p =>
        Some ((SimpleMatchDontCare, inr false) :: nil)
      | p{ goto δ st @ _ }p =>
        Some ((SimpleMatchDontCare, inl st) :: nil)
      | p{ select select_exp { cases } default:=def @ _ }p =>
        let* select_exp' := compile_expression select_exp in
        let fix f cases :=
          match cases with
          | nil =>
            compile_transition def
          | (case_exp, case_trans) :: cases' =>
            let* child_clauses := compile_transition case_trans in
            let* case_exp' := compile_expression case_exp in
            let augmented_clauses :=
              map (
                fun '(clause, target) =>
                (SimpleMatchAnd (SimpleMatchEquals select_exp' case_exp')
                                clause,
                 target)
              ) child_clauses in
            let* tail := f cases' in
            Some (augmented_clauses ++ tail)
          end in
         f cases
      end
    .
    End NotationSection.

    Fixpoint compile_transitions
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (list (string * list (simple_match * (string + bool))))
    :=
      match states with
      | nil =>
        Some nil
      | state :: states' =>
        let '(name, P4cub.Parser.ParserState.State _ trans) := state in
        let* tail := compile_transitions states' in
        let* head := compile_transition trans in
        Some ((name, head) :: tail)
      end
    .

  End compile.

  Record embedded_p4automaton := MkEmbeddedP4Automaton {
    emb_updates: list (string * list state_operation);
    emb_transitions: list (string * list (simple_match * (string + bool)));
  }.

  Definition parser_to_p4automaton
    (parser: P4cub.TopDecl.d tags_t)
    : option embedded_p4automaton
  :=
    match parser with
    | P4cub.TopDecl.TPParser _ _ params _ states _ => (* AST.v change *)
      match params with
      | (pkt_name, P4cub.PAIn pkt_type) ::
        (hdr_name, P4cub.PAOut hdr_type) :: _ =>
        let* updates := compile_updates pkt_name hdr_name states in
        let* transitions := compile_transitions hdr_name states in
        Some {|
          emb_updates := updates;
          emb_transitions := transitions;
        |}
      | _ =>
        None
      end
    | _ =>
      None
    end
  .

End parser_to_p4automaton.
