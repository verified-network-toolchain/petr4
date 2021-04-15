Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.AList.
Require Import Poulet4.Bitwise.

Require Poulet4.HAList.

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

Definition toBits (w: nat) (bs: list bool) : @ValueBase Info :=
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
    | parse_udp => 28
    | parse_tcp => 20
    end
  .
  Definition values := @ValueBase Info.

  Definition marshall (s: states) (bs: list bool) : values :=
    match s with
    | start =>
      let fields :=
        mkEntry "src" (toBits 8 (slice 0 7 bs)) ::
        mkEntry "dst" (toBits 8 (slice 7 15 bs)) ::
        mkEntry "proto" (toBits 4 (slice 16 19 bs)) :: nil
      in ValBaseHeader fields true
    | parse_udp =>
      let fields :=
        mkEntry "sports" (toBits 8 (slice 0 7 bs)) ::
        mkEntry "dport" (toBits 8 (slice 7 15 bs)) ::
        mkEntry "flags" (toBits 4 (slice 16 19 bs)) ::
        mkEntry "seq" (toBits 8 (slice 20 27 bs)) :: nil
      in ValBaseHeader fields true
    | parse_tcp =>
      let fields :=
        mkEntry "sport" (toBits 8 (slice 0 7 bs)) ::
        mkEntry "dport" (toBits 8 (slice 7 15 bs)) ::
        mkEntry "flags" (toBits 8 (slice 16 19 bs)) :: nil
      in ValBaseHeader fields true
    end.

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
    ("seq", values) ::
    nil
  ).

  Definition tcp_hdr := HAList.t (
    ("sport", values) ::
    ("dport", values) ::
    ("flags", values) ::
    nil
  ).

  Definition store' := HAList.t (
    ("ip", ip_hdr) ::
    ("udp", udp_hdr) ::
    ("tcp", tcp_hdr) ::
    nil
  ).

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        HAList.RCons (toBits 8 (slice 0 7 bs)) (
        HAList.RCons (toBits 8 (slice 7 15 bs)) (
        HAList.RCons (toBits 4 (slice 16 19 bs)) (
        HAList.REmp))) in
      HAList.set st (exist _ "ip" I) fields
    | parse_udp =>
      let fields :=
        HAList.RCons (toBits 8 (slice 0 7 bs)) (
        HAList.RCons (toBits 8 (slice 7 15 bs)) (
        HAList.RCons (toBits 4 (slice 16 19 bs)) (
        HAList.RCons (toBits 8 (slice 20 27 bs)) (
        HAList.REmp)))) in
      HAList.set st (exist _ "udp" I) fields
    | parse_tcp =>
      let fields :=
        HAList.RCons (toBits 8 (slice 0 7 bs)) (
        HAList.RCons (toBits 8 (slice 7 15 bs)) (
        HAList.RCons (toBits 8 (slice 16 19 bs)) (
        HAList.REmp))) in
      HAList.set st (exist _ "tcp" I) fields
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      let ip := HAList.get st (exist _ "ip" I) in
      match HAList.get ip (exist _ "proto" I) with
      | ValBaseInt 4 1 => inl parse_udp
      | ValBaseInt 4 0 => inl parse_tcp
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

  Definition combined_hdr := HAList.t (
    ("src", values) ::
    ("dst", values) ::
    ("proto", values) ::
    ("sport", values) ::
    ("dport", values) ::
    ("flags", values) ::
    nil
  ).

  Definition optional_hdr := HAList.t (
    ("seq", values) ::
    nil
  ).

  Definition tcp_hdr := HAList.t (
    ("sport", values) ::
    ("dport", values) ::
    ("flags", values) ::
    nil
  ).

  Definition store' := HAList.t (
    ("comb", combined_hdr) ::
    ("opt_suffix", optional_hdr) ::
    nil
  ).

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        HAList.RCons (toBits 8 (slice 0 7 bs)) (
        HAList.RCons (toBits 8 (slice 7 15 bs)) (
        HAList.RCons (toBits 4 (slice 16 19 bs)) (
        HAList.RCons (toBits 8 (slice 20 27 bs)) (
        HAList.RCons (toBits 8 (slice 28 35 bs)) (
        HAList.RCons (toBits 8 (slice 36 39 bs)) (
        HAList.REmp)))))) in
      HAList.set st (exist _ "comb" I) fields
    | parse_tcp =>
      let fields := HAList.RCons (toBits 8 bs) HAList.REmp in
      HAList.set st (exist _ "opt_suffix" I) fields
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      let combined := HAList.get st (exist _ "comb" I) in
      match HAList.get combined (exist _ "proto" I) with
      | ValBaseInt 4 1 => inr true
      | ValBaseInt 4 0 => inl parse_tcp
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

Inductive candidate:
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
    forall (st1: BabyIPv1.store') ip pref buf1 st2 buf2,
      HAList.get st1 (exist _ "ip" I) = ip ->
      HAList.get ip (exist _ "proto" I) = ValBaseBit 4 0 ->
      pref ++ buf1 = buf2 ->
      List.length pref = 20 ->
      List.length buf2 < 40 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2)

| BisimulationTCPVersusTCP:
    forall st1 buf1 st2 pref buf2,
      buf1 = skipn 20 pref ++ buf2 ->
      List.length pref = 40 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1)
        (inl BabyIPv2.parse_tcp, st2, buf2)

| BisimulationUDPVersusIP:
    forall (st1: BabyIPv1.store') pref ip buf1 st2 buf2,
      HAList.get st1 (exist _ "ip" I) = ip ->
      HAList.get ip (exist _ "proto" I) = ValBaseBit 4 1 ->
      pref ++ buf1 = buf2 ->
      List.length pref = 20 ->
      List.length buf2 < 40 ->
      candidate
        (inl BabyIPv1.parse_udp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2)

| BisimulationFalseVersusStart:
    forall st1 pref buf1 st2 buf2,
      pref = buf2 ->
      List.length pref = 20 ->
      skipn 16 buf2 <> false :: false :: false :: true :: nil ->
      skipn 16 buf2 <> false :: false :: false :: false :: nil ->
      candidate
        (inr false, st1, buf1)
        (inl BabyIPv2.start, st2, buf2 ++ buf1)
.

Opaque skipn.
Opaque firstn.
Opaque HAList.get.
Opaque HAList.set.

Lemma foo:
  forall sig (s: HAList.t sig) k v,
    HAList.get (HAList.set s k v) k = v
.
Admitted.

Lemma candidate_is_bisimulation:
  bisimulation candidate
.
Proof.
  unfold bisimulation; intros.
  induction H; (split; [try easy|]); intros.
  2: { split; intros; inversion H; easy. }
  - unfold step.
    repeat rewrite app_length.
    simpl List.length.
    simpl size.
    do 2 destruct (equiv_dec _ _); try congruence.
    + unfold BabyIPv1.v1_parser.
      unfold transitions.
      unfold update.
      unfold BabyIPv1.update'.
      unfold BabyIPv1.transitions'.
      rewrite foo.
      * apply BisimulationUDPVersusIP.
        -- rewrite override_id.
           now rewrite app_nil_r.
        -- now rewrite override_id.
        -- rewrite override_id.
           rewrite app_length.
           simpl length.
           assumption.
        -- rewrite app_length.
           simpl length.
           lia.
      * apply BisimulationTCPVersusIP.
        -- rewrite override_id.
           now rewrite app_nil_r.
        -- now rewrite override_id.
        -- rewrite override_id.
           rewrite app_length.
           simpl length.
           assumption.
        -- rewrite app_length.
           simpl length.
           lia.
      * replace (buf ++ b :: nil) with ((buf ++ b :: nil) ++ nil) at 2
          by apply app_nil_r.
        apply BisimulationFalseVersusStart; try assumption.
        -- now rewrite override_id.
        -- rewrite override_id.
           rewrite app_length.
           simpl length.
           assumption.
    + exfalso.
      unfold equiv in *.
      lia.
    + constructor.
      unfold equiv, complement in *.
      rewrite app_length.
      simpl.
      lia.
  - simpl.
    constructor.
  - unfold step.
    repeat rewrite app_length.
    simpl length.
    simpl size.
    do 2 destruct (equiv_dec _ _).
    + simpl.
      rewrite override_id.
      destruct (equiv_dec _ _); [|destruct (equiv_dec _ _)].
      * constructor.
      * unfold equiv, complement in *.
        exfalso.
        apply (f_equal (@length bool)) in H.
        rewrite app_length in H.
        lia.
      * unfold equiv, complement in *.
        exfalso.
        apply (f_equal (@length bool)) in H.
        rewrite app_length in H.
        lia.
    + exfalso.
      apply (f_equal (@length _)) in H.
      rewrite app_length in H.
      unfold equiv, complement in *.
      lia.
    + simpl.
      rewrite override_id.
      destruct (equiv_dec _ _); [|destruct (equiv_dec _ _)].
      * rewrite <- H in e0.
        rewrite skipn_app in e0.
        rewrite firstn_app in e0.
        rewrite skipn_length in e0.
        rewrite H in e0.
        assert (length buf2 = 39).
        unfold equiv in e.
        lia.
        rewrite H3 in e0.
        replace (4 - (39 - 16)) with 0 in e0 by reflexivity.
        simpl firstn in e0 at 2.
        rewrite app_nil_r in e0.
        rewrite <- H in e0.
        rewrite skipn_app in e0.
        rewrite firstn_app in e0.
        rewrite skipn_length in e0.
        rewrite H1 in e0.
        replace (4 - (20 - 16)) with 0 in e0 by reflexivity.
        simpl firstn in e0 at 2.
        rewrite app_nil_r in e0.
        rewrite H0 in e0.
        cbv in e0.
        discriminate.
      * constructor.
        -- rewrite app_nil_r.
           rewrite override_id.
           rewrite <- H.
           rewrite <- app_assoc.
           rewrite skipn_app.
           rewrite <- H1.
           rewrite skipn_all.
           rewrite app_nil_l.
           rewrite PeanoNat.Nat.sub_diag.
           simpl skipn.
           reflexivity.
        -- rewrite override_id.
           rewrite app_length.
           simpl length.
           assumption.
      * rewrite <- H in c1.
        rewrite skipn_app in c1.
        rewrite firstn_app in c1.
        rewrite skipn_length in c1.
        rewrite H in c1.
        assert (length buf2 = 39).
        unfold equiv in e.
        lia.
        rewrite H3 in c1.
        replace (4 - (39 - 16)) with 0 in c1 by reflexivity.
        simpl firstn in c1 at 2.
        rewrite app_nil_r in c1.
        rewrite <- H in c1.
        rewrite skipn_app in c1.
        rewrite firstn_app in c1.
        rewrite skipn_length in c1.
        rewrite H1 in c1.
        replace (4 - (20 - 16)) with 0 in c1 by reflexivity.
        simpl firstn in c1 at 2.
        rewrite app_nil_r in c1.
        rewrite H0 in c1.
        cbv in c1.
        exfalso.
        eauto.
    + apply BisimulationTCPVersusIP; try assumption.
      * rewrite app_assoc.
        now rewrite H.
      * unfold equiv, complement in *.
        rewrite app_length.
        simpl.
        lia.
  - unfold step.
    simpl size.
    repeat rewrite app_length.
    simpl length.
    destruct (equiv_dec _ _); destruct (equiv_dec _ _).
    + simpl.
      constructor.
    + exfalso.
      rewrite H in e.
      rewrite app_length in e.
      rewrite skipn_length in e.
      rewrite H0 in e.
      unfold equiv, complement in *.
      lia.
    + exfalso.
      rewrite H in c.
      rewrite app_length in c.
      rewrite skipn_length in c.
      rewrite H0 in c.
      unfold equiv, complement in *.
      lia.
    + constructor.
      * rewrite H.
        rewrite app_assoc.
        reflexivity.
      * assumption.
  - unfold step.
    simpl size.
    repeat rewrite app_length.
    simpl length.
    do 2 destruct (equiv_dec _ _).
    + simpl.
      rewrite override_id.
      destruct (equiv_dec _ _); try constructor.
      rewrite <- H in c.
      rewrite <- app_assoc in c.
      rewrite skipn_app in c.
      rewrite firstn_app in c.
      rewrite skipn_length in c.
      rewrite H1 in c.
      replace (4 - (20 - 16)) with 0 in c by reflexivity.
      simpl firstn in c at 2.
      rewrite app_nil_r in c.
      rewrite H0 in c.
      replace 4 with (length (repeat false 3 ++ true :: nil)) in c by reflexivity.
      rewrite firstn_all in c.
      simpl in c.
      exfalso.
      apply c.
      reflexivity.
    + simpl.
      apply (f_equal (@length _)) in H.
      rewrite app_length in H.
      unfold equiv, complement in *.
      lia.
    + simpl.
      apply (f_equal (@length _)) in H.
      rewrite app_length in H.
      unfold equiv, complement in *.
      lia.
    + constructor; try assumption.
      * rewrite app_assoc.
        rewrite H.
        reflexivity.
      * unfold equiv, complement in *.
        rewrite app_length.
        simpl length.
        lia.
  - simpl.
    rewrite override_id.
    destruct (equiv_dec _ _).
    + destruct (equiv_dec _ _); [|destruct (equiv_dec _ _)].
      * rewrite <- app_assoc in e0.
        rewrite skipn_app in e0.
        rewrite firstn_app in e0.
        rewrite skipn_length in e0.
        rewrite <- H in e0.
        rewrite H0 in e0.
        replace (4 - (20 - 16)) with 0 in e0 by reflexivity.
        simpl firstn in e0 at 2.
        rewrite  H in e0.
        rewrite app_nil_r in e0.
        rewrite firstn_skipn_comm in e0.
        replace (16 + 4) with 20 in e0 by reflexivity.
        rewrite <- H0 in e0.
        rewrite H in e0.
        rewrite firstn_all in e0.
        contradiction.
      * rewrite firstn_skipn_comm in e0.
        replace (16 + 4) with 20 in e0 by reflexivity.
        rewrite <- app_assoc in e0.
        rewrite firstn_app in e0.
        rewrite <- H0 in e0.
        rewrite H in e0.
        replace (length buf2 - length buf2) with 0 in e0 by lia.
        simpl firstn in e0 at 2.
        rewrite app_nil_r in e0.
        rewrite firstn_all in e0.
        contradiction.
      * constructor.
    + rewrite <- app_assoc.
      now constructor.
Qed. *)

(* Theorem babyip_equiv
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
    simpl length.
    lia.
Qed.  *)
