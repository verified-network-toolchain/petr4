Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.BabyIP.

(*
Lemma prebisim_babyip:
  pre_bisimulation BabyIP.aut
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 BabyIP.aut BabyIP1.Start BabyIP2.Start)
                   (inl (inl BabyIP1.Start), [], [])
                   (inl (inr BabyIP2.Start), [], []).
Proof.
  set (rel0 := mk_init 10 BabyIP.aut BabyIP1.Start BabyIP2.Start).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed.
*)
