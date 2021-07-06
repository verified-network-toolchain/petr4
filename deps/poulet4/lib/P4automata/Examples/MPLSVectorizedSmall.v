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

Module MPLSPlain.
  Inductive state :=
  | ParseMPLS
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS; ParseUDP] |}.
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
  | HdrMPLS
  | HdrMPLS1
  | HdrUDP.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrMPLS; HdrMPLS1; HdrUDP] |}.
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
    | ParseMPLS =>
      {| st_op := 
        OpSeq 
          (OpAsgn (HRVar HdrMPLS1) (EHdr (HRVar HdrMPLS)))
          (OpExtract 1 (HRVar HdrMPLS));
         st_trans := P4A.TSel (CExpr (EHdr (HRVar HdrMPLS)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits [false]);
                                 sc_st := inl ParseMPLS |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract 1 (HRVar HdrUDP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSPlain.

Module MPLSUnroll.
  Inductive state :=
  | ParseMPLS0
  | ParseMPLS1
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS0; ParseMPLS1; ParseUDP] |}.
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
  | HdrMPLS
  | HdrMPLS1
  | HdrUDP.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrMPLS; HdrMPLS1; HdrUDP] |}.
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
    | ParseMPLS0 =>
      {| st_op := OpSeq 
        (OpAsgn (HRVar HdrMPLS1) (EHdr (HRVar HdrMPLS)))
        (OpExtract 1 (HRVar HdrMPLS));
         st_trans := P4A.TSel (CExpr (EHdr (HRVar HdrMPLS)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits [false]);
                                 sc_st := inl ParseMPLS1 |}]
                              (inr false) |}
    | ParseMPLS1 =>
      {| st_op := OpSeq 
        (OpAsgn (HRVar HdrMPLS1) (EHdr (HRVar HdrMPLS)))
        (OpExtract 1 (HRVar HdrMPLS));
          st_trans := P4A.TSel (CExpr (EHdr (HRVar HdrMPLS)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits [false]);
                                  sc_st := inl ParseMPLS0 |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract 1 (HRVar HdrUDP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSUnroll.

Module MPLSInline.
  Inductive state :=
  | ParseMPLS
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS; ParseUDP] |}.
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
  | HdrMPLS0
  | HdrMPLS1
  | HdrUDP.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [HdrMPLS0; HdrMPLS1; HdrUDP] |}.
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
    | ParseMPLS =>
      {| st_op := OpSeq 
          (OpExtract 1 (HRVar HdrMPLS0))
          (OpSeq 
            (OpExtract 1 (HRVar HdrMPLS1))
            (OpAsgn (HRVar HdrUDP) (EHdr (HRVar HdrMPLS1)))
          );
         st_trans := P4A.TSel (CPair 
            (CExpr (EHdr (HRVar HdrMPLS0)))
            (CExpr (EHdr (HRVar HdrMPLS1))))
            [{| sc_pat := PPair (PExact (VBits [true])) PAny;
                sc_st := inr true |};
             {| sc_pat := PPair (PExact (VBits [false])) (PExact (VBits [true]));
                sc_st := inl ParseUDP |};
              {| sc_pat := PPair (PExact (VBits [false])) (PExact (VBits [false]));
                sc_st := inl ParseMPLS |}]
            (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract 1 (HRVar HdrUDP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSInline.

Module MPLSVect.
  Definition aut := Sum.sum MPLSPlain.aut MPLSUnroll.aut.
End MPLSVect.

Module MPLSVectUnroll.
  Definition aut := Sum.sum MPLSPlain.aut MPLSInline.aut.
End MPLSVectUnroll.
