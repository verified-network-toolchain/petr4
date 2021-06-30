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
  Inductive state: Type :=
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

  Inductive header: Type :=
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
  Next Obligation.
    unfold st_start.
    cbv.
    Lia.lia.
  Qed.
  
End Simple. 

Module Split.
  Inductive state: Type :=
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
  Next Obligation.
    destruct s; cbv; Lia.lia.
  Qed.
  
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

Module BabyIP1.
  Inductive state :=
  | Start
  | ParseUDP
  | ParseTCP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; ParseUDP; ParseTCP] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | HdrIP
  | HdrUDPTCP.
  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrIP; HdrUDPTCP] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract 20 (HRVar HdrIP);
         st_trans := P4A.TSel (ESlice (EHdr (HRVar HdrIP)) 20 16)
                              [{| sc_val := VBits [false; false; false; true];
                                 sc_st := inl ParseUDP |};
                              {| sc_val := VBits [false; false; false; false];
                                 sc_st := inl ParseTCP |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract 20 (HRVar HdrUDPTCP);
         st_trans := P4A.TGoto _ (inr true) |}
    | ParseTCP =>
      {| st_op := OpExtract 28 (HRVar HdrUDPTCP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

End BabyIP1.

Module BabyIP2.
End BabyIP2.

Module MPLS1.
End MPLS1.

Module MPLS2.
End MPLS2.

Module TPP1.
End TPP1.

Module TPP2.
End TPP2.
