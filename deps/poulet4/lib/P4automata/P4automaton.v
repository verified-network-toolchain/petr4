Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Compare_dec.

Record p4automaton := MkP4Automaton {
  store: Type;
  states: Type;
  size: states -> nat;
  update: states -> list bool -> store -> store;
  transitions: states -> store -> states + bool;
  cap: forall s, 0 < size s;
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
    if length buf' == size a state
    then
      let st' := update a state buf' st in
      let state' := transitions a state st' in
      (state', st', nil)
    else (inl state, st, buf')
  | inr halt =>
    (inr halt, st, buf ++ b :: nil)
  end
.

Lemma step_with_space
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf: list bool)
  (b: bool)
:
  length buf + 1 < size a s ->
  step (inl s, st, buf) b = (inl s, st, buf ++ b :: nil)
.
Proof.
  intros; simpl.
  destruct (equiv_dec _ _); auto.
  unfold equiv in e.
  rewrite app_length in e.
  simpl length in e.
  lia.
Qed.

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

Lemma follow_nil
  {a: p4automaton}
  (c: configuration a)
:
  follow c nil = c
.
Proof.
  reflexivity.
Qed.

Lemma follow_with_space
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf buf': list bool)
  (b: bool)
:
  length buf + 1 < size a s ->
  follow (inl s, st, buf) (b :: buf') =
  follow (inl s, st, buf ++ b :: nil) buf'
.
Proof.
  intros.
  rewrite follow_cons.
  f_equal.
  now apply step_with_space.
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
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  forall input,
    accepted c1 input <->
    accepted c2 input
.

Definition rel (a1 a2: p4automaton) :=
  configuration a1 -> configuration a2 -> Prop
.

Definition bisimulation
  {a1 a2: p4automaton}
  (R: rel a1 a2)
:=
  forall c1 c2,
    R c1 c2 ->
      (accepting c1 <-> accepting c2) /\
      forall b, R (step c1 b) (step c2 b)
.

Definition bisimilar
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  exists R, bisimulation R /\ R c1 c2
.

Lemma bisimilar_implies_equiv
  {a1 a2: p4automaton}
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
  {a1 a2: p4automaton}
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
  {a1 a2: p4automaton}
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
  {a1 a2: p4automaton}
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

Definition bisimulation_upto
  {a1 a2: p4automaton}
  (f: rel a1 a2 -> rel a1 a2)
  (R: rel a1 a2)
:=
  forall c1 c2,
    R c1 c2 ->
      (accepting c1 <-> accepting c2) /\
      forall b, f R (step c1 b) (step c2 b)
.

Definition bisimilar_upto
  {a1 a2: p4automaton}
  (f: rel a1 a2 -> rel a1 a2)
  (c1: configuration a1)
  (c2: configuration a2)
:=
  exists R, bisimulation_upto f R /\ R c1 c2
.

Definition closure_extends
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2) c1 c2,
    R c1 c2 -> close R c1 c2
.

Definition closure_preserves_accept
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2),
    (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
    (forall c1 c2, close R c1 c2 -> accepting c1 <-> accepting c2)
.

Definition closure_preserves_transition
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2),
    (forall c1 c2, R c1 c2 ->
     forall b, close R (step c1 b) (step c2 b)) ->
    (forall c1 c2, close R c1 c2 ->
     forall b, close R (step c1 b) (step c2 b))
.

Definition closure_mono
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R R': rel a1 a2),
    (forall c1 c2, R c1 c2 -> R' c1 c2) ->
    (forall c1 c2, close R c1 c2 -> close R' c1 c2)
.

Class SoundClosure
  {a1 a2: p4automaton}
  (f: rel a1 a2 -> rel a1 a2)
:= {
  closure_sound_extends: closure_extends f;
  closure_sound_preserves_accept: closure_preserves_accept f;
  closure_sound_preserves_transition: closure_preserves_transition f;
  closure_sound_mono: closure_mono f;
}.

Lemma bisimilar_implies_bisimilar_upto
  {a1 a2: p4automaton}
  (f: rel a1 a2 -> rel a1 a2)
:
  SoundClosure f ->
  forall c1 c2,
    bisimilar c1 c2 ->
    bisimilar_upto f c1 c2
.
Proof.
  intros.
  destruct H0 as [R [? ?]].
  exists R; split; auto.
  intros c1' c2' ?; split.
  - now apply H0.
  - intros.
    now apply H, H0.
Qed.

Lemma bisimilar_upto_implies_bisimilar
  {a1 a2: p4automaton}
  (f: rel a1 a2 -> rel a1 a2)
:
  SoundClosure f ->
  forall c1 c2,
    bisimilar_upto f c1 c2 ->
    bisimilar c1 c2
.
Proof.
  intros.
  destruct H0 as [R [? ?]].
  exists (f R); split.
  - intros c1' c2' ?; split.
    + revert c1' c2' H2.
      now apply H, H0.
    + revert c1' c2' H2.
      now apply H, H0.
  - now apply closure_sound_extends.
Qed.


(* Sanity check: the identity function is a valid closure. *)
Definition close_id
  {a1 a2: p4automaton}
  (R: rel a1 a2)
:=
  R
.

Program Instance close_id_sound
    {a1 a2: p4automaton}
    : @SoundClosure a1 a2 close_id
.
Solve Obligations with firstorder.

Inductive close_interpolate
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  : configuration a1 -> configuration a2 -> Prop
:=
| InterpolateBase:
    forall c1 c2,
      R c1 c2 -> close_interpolate _ c1 c2
| InterpolateStep:
    forall s1 st1 buf1 s2 st2 buf2 b,
      close_interpolate _ (inl s1, st1, buf1)
                          (inl s2, st2, buf2) ->
      length buf1 + 1 < size a1 s1 ->
      length buf2 + 1 < size a2 s2 ->
      (forall buf,
         length buf = min (size a1 s1 - length buf1)
                          (size a2 s2 - length buf2) ->
         R (follow (inl s1, st1, buf1) buf)
           (follow (inl s2, st2, buf2) buf)) ->
      close_interpolate _ (inl s1, st1, buf1 ++ b :: nil)
                          (inl s2, st2, buf2 ++ b :: nil)
.

Program Instance close_interpolate_sound
    {a1 a2: p4automaton}
    : @SoundClosure a1 a2 close_interpolate
.
Next Obligation.
  intros ? ? ? ?.
  eauto using InterpolateBase.
Qed.
Next Obligation.
  intros ? ? ? ? ?.
  induction H0; firstorder.
Qed.
Next Obligation.
  intros ? ? ? ? ?.
  induction H0; intros; eauto.
  repeat rewrite <- step_with_space; auto.
  destruct (le_lt_dec (Nat.min (size a1 s1 - length buf1)
                               (size a2 s2 - length buf2)) 2).
  - apply InterpolateBase.
    rewrite <- follow_nil.
    rewrite <- follow_nil at 1.
    repeat rewrite <- follow_cons.
    apply H3.
    simpl length.
    lia.
  - repeat rewrite step_with_space;
    repeat rewrite app_length;
    simpl length;
    try lia.
    apply InterpolateStep;
    repeat rewrite app_length;
    simpl length;
    try lia.
    + repeat rewrite <- step_with_space; auto.
    + intros.
       repeat rewrite <- follow_with_space; try lia.
       apply H3.
       simpl length.
       lia.
Qed.
Next Obligation.
  intros ? ? ? ? ? ?.
  induction H0.
  - eauto using InterpolateBase.
  - eauto using InterpolateStep.
Qed.

Definition min_step
  {a: p4automaton}
  (c: configuration a)
:=
  match c with
  | (inl s, _, buf) =>
    max (size a s - length buf) 1
  | (inr _, _, _) =>
    1
  end
.

Definition bisimulation_with_leaps
  {a1 a2: p4automaton}
  (R: rel a1 a2)
:=
  forall c1 c2,
    R c1 c2 ->
      (accepting c1 <-> accepting c2) /\
      forall buf,
        length buf = min (min_step c1) (min_step c2) ->
        R (follow c1 buf) (follow c2 buf)
.

Definition bisimilar_with_leaps
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  exists R,
    R c1 c2 /\ bisimulation_with_leaps R
.

Lemma bisimilar_with_leaps_implies_bisimilar_upto
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  bisimilar_with_leaps c1 c2 ->
  bisimilar_upto close_interpolate c1 c2
.
Proof.
  intros.
  destruct H as [R [? ?]].
  exists R.
  split; auto.
  intros c1' c2' ?; split.
  - now apply H0.
  - intros.
    rewrite <- follow_nil.
    rewrite <- follow_nil at 1.
    repeat rewrite <- follow_cons.
    destruct c1' as (([s1' | h1'], st1'), buf1'),
             c2' as (([s2' | h2'], st2'), buf2').
    + destruct (le_lt_dec 2 (min (min_step (inl s1', st1', buf1'))
                                 (min_step (inl s2', st2', buf2')))).
      * repeat rewrite follow_with_space.
        all: unfold min_step; simpl in l; try lia.
        apply InterpolateStep; try lia.
        now apply InterpolateBase.
        intros.
        apply H0; auto.
        simpl min_step.
        lia.
      * apply InterpolateBase, H0; auto.
        simpl min_step in *.
        simpl length.
        lia.
    + apply InterpolateBase, H0; auto.
      simpl min_step in *.
      simpl length.
      lia.
    + apply InterpolateBase, H0; auto.
      simpl min_step in *.
      simpl length.
      lia.
    + apply InterpolateBase.
      apply H0; auto.
Qed.

Lemma bisimilar_implies_bisimilar_with_leaps
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  bisimilar c1 c2 ->
  bisimilar_with_leaps c1 c2
.
Proof.
  intros.
  destruct H as [R [? ?]].
  exists R.
  split; auto.
  intros c1' c2' ?; split.
  - now apply H.
  - intros.
    clear H2.
    induction buf using rev_ind.
    + now repeat rewrite follow_nil.
    + unfold follow.
      repeat rewrite fold_left_app.
      fold (follow c1' buf).
      fold (follow c2' buf).
      simpl fold_left.
      now apply H.
Qed.

Theorem bisimilar_iff_bisimilar_with_leaps
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:
  bisimilar c1 c2 <->
  bisimilar_with_leaps c1 c2
.
Proof.
  split; intro.
  - now apply bisimilar_implies_bisimilar_with_leaps.
  - apply bisimilar_upto_implies_bisimilar with (f := close_interpolate).
    + apply close_interpolate_sound.
    + now apply bisimilar_with_leaps_implies_bisimilar_upto.
Qed.

Lemma follow_buffer
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf buf': list bool)
:
  Datatypes.length buf + Datatypes.length buf' + 1 < size a s ->
  follow (inl s, st, buf) buf' =
  (inl s, st, buf ++ buf')
.
Proof.
  induction buf' using rev_ind; intros.
  - now rewrite follow_nil, app_nil_r.
  - unfold follow.
    rewrite fold_left_app.
    fold (follow (inl s, st, buf) buf').
    simpl fold_left.
    rewrite IHbuf'.
    + rewrite step_with_space.
      * now rewrite app_assoc.
      * rewrite app_length in *.
        simpl in *.
        lia.
    + rewrite app_length in *.
      simpl Datatypes.length in *.
      lia.
Qed.

Lemma follow_exact
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf buf': list bool)
:
  Datatypes.length buf' > 0 ->
  Datatypes.length buf + Datatypes.length buf' = size a s ->
  follow (inl s, st, buf) buf' =
    let st' := update a s (buf ++ buf') st in
    (transitions a s st', st', nil)
.
Proof.
  intros.
  destruct buf'.
  - simpl Datatypes.length in H.
    lia.
  - revert s st buf b H H0.
    induction buf'; intros.
    + rewrite follow_cons, follow_nil.
      unfold step.
      rewrite app_length.
      simpl Datatypes.length in *.
      destruct (equiv_dec _ _); trivial.
      exfalso; eapply c; auto.
      
    + rewrite follow_cons.
      rewrite step_with_space.
      rewrite IHbuf'.
      * repeat f_equal;
        rewrite <- app_assoc;
        rewrite <- app_comm_cons;
        rewrite app_nil_l;
        easy.
      * simpl Datatypes.length in *.
        lia.
      * rewrite app_length in *.
        simpl Datatypes.length in *.
        lia.
      * simpl Datatypes.length in *.
        lia.
Qed.