Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Set Universe Polymorphism.

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
