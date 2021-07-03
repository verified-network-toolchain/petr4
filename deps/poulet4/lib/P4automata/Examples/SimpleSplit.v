Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Simple.
  Inductive state: Set :=
  | Start.

  Global Program Instance state_eq_dec: EquivDec.EqDec state eq :=
    fun x y => match x, y with
            | Start, Start => in_left
            end.

  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header: Set :=
  | HdrSimple.

  Global Program Instance header_eq_dec: EquivDec.EqDec header eq :=
    fun x y => match x, y with
            | HdrSimple, HdrSimple => in_left
            end.

  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrSimple] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition st_start: Syntax.state state header :=
    {| st_op := OpExtract 16 (HRVar HdrSimple);
       st_trans := TGoto _ (inr true) |}.

  Program Definition aut: Syntax.t state header :=
    {| t_states x := st_start |}.
  Solve Obligations with (unfold st_start; cbv; Lia.lia).
  
End Simple. 

Module Split.
  Inductive state: Set :=
  | StSplit1
  | StSplit2.

  Global Program Instance state_eq_dec: EquivDec.EqDec state eq :=
    fun x y => match x, y with
            | StSplit1, StSplit1
            | StSplit2, StSplit2 => in_left
            | _, _ => in_right
            end.
  Solve Obligations with prep_equiv; try destruct x; destruct y; intuition congruence.

  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [StSplit1; StSplit2] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes.
    intro H; inversion H; discriminate || assumption.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header: Set :=
  | HdrSplit1
  | HdrSplit2.

  Global Program Instance header_eq_dec: EquivDec.EqDec header eq :=
    fun x y => match x, y with
            | HdrSplit1, HdrSplit1
            | HdrSplit2, HdrSplit2 => in_left
            | _, _ => in_right
            end.
  Solve Obligations with prep_equiv; try destruct x; destruct y; intuition congruence.

  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrSplit1; HdrSplit2] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes.
    intro H; inversion H; discriminate || assumption.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition st_split1: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit1);
       st_trans := TGoto _ (inl StSplit2) |}.

  Definition st_split2: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit2);
       st_trans := TGoto _ (inr true) |}.

  Program Definition aut: Syntax.t state header :=
    {| t_states s :=
         match s with
         | StSplit1 => st_split1
         | StSplit2 => st_split2
         end |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
  
End Split.

Module SimpleSplit.
  Definition state: Type := Sum.S Simple.state Split.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H Simple.header Split.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := sum Simple.aut Split.aut.
  
End SimpleSplit.
