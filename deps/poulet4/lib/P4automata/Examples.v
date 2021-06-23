Require Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Simple.
  Inductive state: Type :=
  | Start.

  Program Instance state_eq_dec: EquivDec.EqDec state eq :=
    fun x y => match x, y with
            | Start, Start => in_left
            end.

  Inductive header: Type :=
  | HdrSimple.

  Global Program Instance header_eq_dec: EquivDec.EqDec header eq :=
    fun x y => match x, y with
            | HdrSimple, HdrSimple => in_left
            end.

  Definition st_start: Syntax.state state header :=
    {| st_op := OpExtract 16 (HRVar HdrSimple);
       st_trans := TGoto _ (inr true) |}.

  Definition aut: Syntax.t state header :=
    Env.bind Start st_start (Env.empty _ _).
End Simple. 

Module Split.
  Inductive state: Type :=
  | StSplit1
  | StSplit2.

  Program Instance state_eq_dec: EquivDec.EqDec state eq :=
    fun x y => match x, y with
            | StSplit1, StSplit1
            | StSplit2, StSplit2 => in_left
            | _, _ => in_right
            end.
  Solve Obligations with prep_equiv; try destruct x; destruct y; intuition congruence.

  Inductive header: Type :=
  | HdrSplit1
  | HdrSplit2.

  Global Program Instance header_eq_dec: EquivDec.EqDec header eq :=
    fun x y => match x, y with
            | HdrSplit1, HdrSplit1
            | HdrSplit2, HdrSplit2 => in_left
            | _, _ => in_right
            end.
  Solve Obligations with prep_equiv; try destruct x; destruct y; intuition congruence.

  Definition st_split1: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit1);
       st_trans := TGoto _ (inl StSplit2) |}.

  Definition st_split2: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit2);
       st_trans := TGoto _ (inr true) |}.

  Definition aut: Syntax.t state header :=
    Env.bind StSplit1 st_split1 (Env.bind StSplit2 st_split2 (Env.empty _ _)).
End Split.

Module SimpleSplit.
  Definition state: Type := Sum.S Simple.state Split.state.
  Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H Simple.header Split.header.
  Instance header_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition aut := Eval cbv in sum Simple.aut Split.aut.
End SimpleSplit.

