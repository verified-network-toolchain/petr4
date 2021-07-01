Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Poulet4.Relations.

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

Definition size' {a: p4automaton} (s: a.(states) + bool) : nat :=
  match s with
  | inl s => a.(size) s
  | inr _ => 1
  end.

Definition step
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  : configuration a
:=
  let '(state, st, buf) := c in
  let buf' := buf ++ b :: nil in
  if length buf' == size' state
  then
    match state with
    | inl state =>
      let st' := update a state buf' st in
      let state' := transitions a state st' in
      (state', st', nil)
    | inr b =>
      (inr false, st, nil)
    end
  else (state, st, buf')
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
  unfold "===" in e.
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

Definition rel a1 a2 := configuration a1 -> configuration a2 -> Prop.
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
