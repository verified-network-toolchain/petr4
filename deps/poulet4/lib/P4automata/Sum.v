Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.FinType.
Require Import Poulet4.HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section Sum.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  (* Header identifiers. *)
  Variable (H1: Type).
  Context `{H1_eq_dec: EquivDec.EqDec H1 eq}.
  Variable (H2: Type).
  Context `{H2_eq_dec: EquivDec.EqDec H2 eq}.

  Variable (a1: Syntax.t S1 H1).
  Variable (a2: Syntax.t S2 H2).

  Definition S : Type := S1 + S2.

  Global Instance S_eq_dec: EquivDec.EqDec S eq :=
    ltac:(typeclasses eauto).

  Global Instance S_finite: @Finite S _ S_eq_dec :=
    ltac:(typeclasses eauto).

  Definition H : Type := H1 + H2.

  Global Instance H_eq_dec: EquivDec.EqDec H eq :=
    ltac:(typeclasses eauto).

  Program Definition sum : Syntax.t S H :=
    {| Syntax.t_states s :=
         match s with
         | inl s1 => Syntax.state_fmapSH inl inl (a1.(Syntax.t_states) s1)
         | inr s2 => Syntax.state_fmapSH inr inr (a2.(Syntax.t_states) s2)
         end |}.
  Next Obligation.
    destruct a1, a2, s;
      simpl;
      erewrite Syntax.op_fmapH_nonempty; eauto.
  Qed.
  Next Obligation.
    destruct a1, a2, s;
      erewrite Syntax.state_fmapSH_size; eauto.
  Qed.
End Sum.
