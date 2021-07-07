Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.MPLSVectorized.

Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ [] _ _ =>
    idtac "close";
    time apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ (_ :: _) _ _ =>
    idtac "skip";
    time pbskip'
  | |- pre_bisimulation ?a ?wp ?R (?C :: ?T) ?a1 ?a2 =>
    idtac "extend";
    let t := fresh "tmp" in
    let Heqwp := fresh "Heqwp" in
    let Hext := fresh "Hext" in
    time pose (t := wp a C);
      time assert (Heqwp: t = wp a C) by reflexivity;
      time cbv in t;
      time pose proof (Hext := fun R' T' pf => PreBisimulationExtend _ _ _ MPLSVect.aut (WPSymLeap.wp (H:=Sum.H MPLSPlain.header MPLSUnroll.header)) R' T' C t a1 a2 Heqwp pf);
      time unfold t in Hext;
      time apply (Hext R T);
      time clear Hext t Heqwp;
      time simpl (_ ++ _)
  end.


(* John: this takes ~30 minutes on my laptop to solve *)
(* Lemma prebisim_mpls_unroll:
  pre_bisimulation MPLSVect.aut
                   (WPSymLeap.wp (H:=_))
                   (separated _ _ _ MPLSVect.aut)
                   nil
                   (mk_init 10 MPLSVect.aut MPLSPlain.ParseMPLS MPLSUnroll.ParseMPLS0)
                   (inl (inl MPLSPlain.ParseMPLS), [], [])
                   (inl (inr MPLSUnroll.ParseMPLS0), [], []).
Proof.
  set (rel0 := mk_init 10 MPLSVect.aut MPLSPlain.ParseMPLS MPLSUnroll.ParseMPLS0).
  cbv in rel0.
  subst rel0.
  solve_bisim'.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Time Qed. *)


(* John: I haven't timed this one yet *)

(* Lemma prebisim_mpls_vect_unroll:
  pre_bisimulation MPLSVectUnroll.aut
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 MPLSVectUnroll.aut MPLSPlain.ParseMPLS MPLSInline.ParseMPLS)
                   (inl (inl MPLSPlain.ParseMPLS), [], [])
                   (inl (inr MPLSInline.ParseMPLS), [], []).
Proof.
  set (rel0 := mk_init 10 MPLSVectUnroll.aut MPLSPlain.ParseMPLS MPLSInline.ParseMPLS).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed. *)
