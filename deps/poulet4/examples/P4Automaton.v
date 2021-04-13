Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.

Definition store (names: Type) := names -> list bool.

Record p4automaton := MkP4Automaton {
  states: Type;
  names: Type;
  eq_name: EqDec names eq;
  size: names -> nat;
  extract: states -> names;
  transitions: states -> store names -> states + bool;
}.

Definition coproduct (a1 a2: p4automaton) := {|
  states := states a1 + states a2;
  names := names a1 + names a2;
  eq_name := sum_eqdec (eq_name a1) (eq_name a2);
  size := fun n =>
    match n with
    | inl n => size a1 n
    | inr n => size a2 n
    end;
  extract := fun s =>
    match s with
    | inl s => inl (extract a1 s)
    | inr s => inr (extract a2 s)
    end;
  transitions := fun s st =>
    match s with
    | inl s =>
      match transitions a1 s (fun n => st (inl n)) with
      | inl s' => inl (inl s)
      | inr b => inr b
      end
    | inr s =>
      match transitions a2 s (fun n => st (inr n)) with
      | inl s' => inl (inr s)
      | inr b => inr b
      end
    end
|}.

Definition configuration (a: p4automaton) : Type :=
  (states a + bool) * store (names a) * (list bool)
.

Definition override
  {names: Type}
  (eq_dec: EqDec names eq)
  (st: store names)
  (name: names)
  (val: list bool)
  : store names
:=
  fun name' =>
    if eq_dec name name'
    then val
    else st name'
.

Lemma override_id
  {names: Type}
  (eq_dec: EqDec names eq)
  (st: store names)
  (name: names)
  (val: list bool)
:
  override eq_dec st name val name = val
.
Proof.
  unfold override.
  destruct (eq_dec name name); congruence.
Qed.

Definition step
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  : configuration a
:=
  let '(state, st, buf) := c in
  match state with
  | inl state =>
    let name := extract a state in
    let buf' := buf ++ b :: nil in
    if length buf' == size a name
    then let st' := override (eq_name a) st name buf' in
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

Module BabyIPv1.
  Inductive states :=
  | start
  | parse_udp
  | parse_tcp
  .

  Inductive names :=
  | ip
  | tcp
  | udp
  .

  Scheme Equality for names.

  Definition sizes (n: names) : nat :=
    match n with
    | ip => 20
    | tcp => 28
    | udp => 20
    end
  .

  Definition extract (s: states) : names :=
    match s with
    | start => ip
    | parse_udp => udp
    | parse_tcp => tcp
    end
  .

  Definition transition (s: states) (st: store names) : states + bool :=
    match s with
    | start =>
      let proto := skipn 16 (st ip) in
      if proto == false :: false :: false :: true :: nil
      then inl parse_udp
      else if proto == false :: false :: false :: false :: nil
      then inl parse_tcp
      else inr false
    | parse_udp => inr true
    | parse_tcp => inr true
    end
  .
End BabyIPv1.

Definition v1_parser := {|
  states := BabyIPv1.states;
  names := BabyIPv1.names;
  eq_name := BabyIPv1.names_eq_dec;
  size := BabyIPv1.sizes;
  extract := BabyIPv1.extract;
  transitions := BabyIPv1.transition
|}.

Module BabyIPv2.
  Inductive states :=
  | start
  | parse_tcp
  .

  Inductive names :=
  | comb
  | opt_stuff
  .

  Scheme Equality for names.

  Definition sizes (n: names) : nat :=
    match n with
    | comb => 40
    | opt_stuff => 8
    end
  .

  Definition extract (s: states) : names :=
    match s with
    | start => comb
    | parse_tcp => opt_stuff
    end
  .

  Definition transition (s: states) (st: store names) : states + bool :=
    match s with
    | start =>
      let proto := firstn 4 (skipn 16 (st comb)) in
      if proto == false :: false :: false :: true :: nil
      then inr true
      else if proto == false :: false :: false :: false :: nil
      then inl parse_tcp
      else inr false
    | parse_tcp => inr true
    end
  .
End BabyIPv2.

Definition v2_parser := {|
  states := BabyIPv2.states;
  names := BabyIPv2.names;
  eq_name := BabyIPv2.names_eq_dec;
  size := BabyIPv2.sizes;
  extract := BabyIPv2.extract;
  transitions := BabyIPv2.transition
|}.

Inductive candidate:
  configuration v1_parser ->
  configuration v2_parser ->
  Prop
:=
| BisimulationStart:
    forall st1 st2 buf,
      length buf < 20 ->
      candidate
        (inl BabyIPv1.start, st1, buf)
        (inl BabyIPv2.start, st2, buf)
| BisimulationEnd:
    forall st1 st2 buf1 buf2 b,
      candidate
        (inr b, st1, buf1)
        (inr b, st2, buf2)
| BisimulationTCPVersusIP:
    forall st1 st2 buf1 buf2,
      st1 BabyIPv1.ip ++ buf1 = buf2 ->
      skipn 16 (st1 BabyIPv1.ip) = repeat false 4 ->
      length (st1 BabyIPv1.ip) = 20 ->
      length buf2 < 40 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2)
| BisimulationTCPVersusTCP:
    forall st1 st2 buf1 buf2,
      buf1 = skipn 20 (st2 BabyIPv2.comb) ++ buf2 ->
      length (st2 BabyIPv2.comb) = 40 ->
      candidate
        (inl BabyIPv1.parse_tcp, st1, buf1)
        (inl BabyIPv2.parse_tcp, st2, buf2)
| BisimulationUDPVersusIP:
    forall st1 st2 buf1 buf2,
      st1 BabyIPv1.ip ++ buf1 = buf2 ->
      skipn 16 (st1 BabyIPv1.ip) = repeat false 3 ++ true :: nil ->
      length (st1 BabyIPv1.ip) = 20 ->
      length buf2 < 40 ->
      candidate
        (inl BabyIPv1.parse_udp, st1, buf1)
        (inl BabyIPv2.start, st2, buf2)
| BisimulationFalseVersusStart:
    forall st1 st2 buf1 buf2,
      st1 (BabyIPv1.ip) = buf2 ->
      length (st1 (BabyIPv1.ip)) = 20 ->
      skipn 16 buf2 <> false :: false :: false :: true :: nil ->
      skipn 16 buf2 <> false :: false :: false :: false :: nil ->
      candidate
        (inr false, st1, buf1)
        (inl BabyIPv2.start, st2, buf2 ++ buf1)
.

Lemma candidate_is_bisimulation:
  bisimulation candidate
.
Proof.
  unfold bisimulation; intros.
  induction H; (split; [simpl; try easy; split; intros; try inversion H; congruence|]); intros.
  - unfold step.
    repeat rewrite app_length.
    simpl length.
    simpl size.
    do 2 destruct (equiv_dec _ _); try congruence.
    + unfold transitions.
      unfold v1_parser.
      simpl eq_name.
      simpl extract.
      unfold BabyIPv1.transition.
      rewrite override_id.
      destruct (equiv_dec _ _); [|destruct (equiv_dec _ _)].
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
    + unfold transitions.
      unfold v1_parser, v2_parser.
      simpl eq_name.
      simpl extract.
      unfold BabyIPv1.transition, BabyIPv2.transition.
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
    + unfold transitions.
      unfold v2_parser.
      simpl override.
      simpl extract.
      unfold BabyIPv2.transition.
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
    + unfold transitions.
      unfold v1_parser, v2_parser.
      simpl eq_name.
      simpl extract.
      unfold BabyIPv1.transition.
      unfold BabyIPv2.transition.
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
    unfold transitions.
    unfold v1_parser, v2_parser.
    simpl eq_name.
    simpl extract.
    unfold BabyIPv1.transition, BabyIPv2.transition.
    repeat rewrite override_id.
    destruct (equiv_dec _ _).
    * destruct (equiv_dec _ _).
      destruct (equiv_dec _ _); try constructor.
      destruct (equiv_dec _ _).
      -- rewrite <- H in e1.
         rewrite <- app_assoc in e1.
         rewrite skipn_app in e1.
         rewrite firstn_app in e1.
         rewrite H0 in e1.
         simpl length in e1.
         replace (4 - 4) with 0 in e1 by reflexivity.
         simpl firstn in e1 at 2.
         rewrite app_nil_r in e1.
         cbv in e1.
         discriminate.
      -- rewrite <- H in c.
         rewrite <- app_assoc in c.
         rewrite skipn_app in c.
         rewrite firstn_app in c.
         rewrite skipn_length in c.
         rewrite H1 in c.
         replace (4 - (20 - 16)) with 0 in c by reflexivity.
         simpl firstn in c at 2.
         rewrite app_nil_r in c.
         rewrite H0 in c.
         cbv in c.
         exfalso.
         eauto.
      -- apply (f_equal (@length _)) in H.
         rewrite app_length in H.
         unfold equiv, complement in *.
         lia.
    * destruct (equiv_dec _ _); [destruct (equiv_dec _ _);[|destruct (equiv_dec _ _)]|].
      -- apply (f_equal (@length _)) in H.
         rewrite app_length in H.
         unfold equiv, complement in *.
         lia.
      -- apply (f_equal (@length _)) in H.
         rewrite app_length in H.
         unfold equiv, complement in *.
         lia.
      -- rewrite <- H in c0.
         rewrite <- app_assoc in c0.
         rewrite skipn_app in c0.
         rewrite H1 in c0.
         replace (16 - 20) with 0 in c0 by reflexivity.
         simpl skipn in c0 at 2.
         rewrite firstn_app in c0.
         rewrite skipn_length in c0.
         rewrite H1 in c0.
         replace (4 - (20 - 16)) with 0 in c0 by reflexivity.
         simpl firstn in c0 at 2.
         rewrite app_nil_r in c0.
         rewrite H0 in c0.
         cbv in c0.
         exfalso.
         eauto.
      -- constructor; try assumption.
         ** rewrite app_assoc.
            rewrite H.
            reflexivity.
         ** rewrite app_length.
            simpl length.
            unfold equiv, complement in *.
            lia.
  - unfold step.
    simpl size.
    rewrite app_length.
    simpl length.
    unfold transitions.
    unfold v2_parser.
    simpl eq_name.
    simpl extract.
    destruct (equiv_dec _ _).
    + unfold BabyIPv2.transition.
      rewrite override_id.
      destruct (equiv_dec _ _); [|destruct (equiv_dec _ _)].
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
Qed.

Theorem babyip_equiv
  (st1: store BabyIPv1.names)
  (st2: store BabyIPv2.names)
:
  @lang_equiv v1_parser
              v2_parser
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
Qed.
