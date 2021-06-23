Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4cub.BigStep.BSUtil.
Require Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section Sum.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.

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

  Definition H : Type := H1 + H2.

  Global Instance H_eq_dec: EquivDec.EqDec H eq :=
    ltac:(typeclasses eauto).

  Definition sum : Syntax.t S H :=
    Envn.Env.scope_shadow (Syntax.t_fmapSH inl inl a1)
                          (Syntax.t_fmapSH inr inr a2).
End Sum.
