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
         st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar HdrIP)) 19 16))
                              [{| sc_pat := PExact (VBits [false; false; false; true]);
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits [false; false; false; false]);
                                 sc_st := inl ParseTCP |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract 20 (HRVar HdrUDPTCP);
         st_trans := P4A.TGoto _ (inr true) |}
    | ParseTCP =>
      {| st_op := OpExtract 28 (HRVar HdrUDPTCP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BabyIP1.

Module BabyIP2.
  Inductive state :=
  | Start
  | ParseSeq.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; ParseSeq] |}.
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
  | HdrCombi
  | HdrSeq.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrCombi; HdrSeq] |}.
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
      {| st_op := OpExtract 40 (HRVar HdrCombi);
         st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar HdrCombi)) 19 16))
                              [{| sc_pat := PExact (VBits [false; false; false; true]);
                                  sc_st := inr true |};
                              {| sc_pat := PExact (VBits [false; false; false; false]);
                                 sc_st := inl ParseSeq |}]
                              (inr false) |}
    | ParseSeq =>
      {| st_op := OpExtract 8 (HRVar HdrSeq);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BabyIP2.

Module BabyIP.
  Definition aut := Sum.sum BabyIP1.aut BabyIP2.aut.
End BabyIP.
