Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.BabyIP.
Require Import Poulet4.P4automata.Examples.IPFilter.

(* 
Lemma prebisim_babyip:
  pre_bisimulation BabyIP.aut
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 BabyIP.aut BabyIP1.Start BabyIP2.Start)
                   (inl (inl BabyIP1.Start), [], [])
                   (inl (inr BabyIP2.Start), [], []).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := mk_init 10 BabyIP.aut BabyIP1.Start BabyIP2.Start).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed. *)
(* 
Lemma prebisim_ipfilter:
  pre_bisimulation IPFilter.aut
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 IPFilter.aut UDPCombined.Parse UDPInterleaved.ParseIP)
                   (inl (inl UDPCombined.Parse), [], [])
                   (inl (inr UDPInterleaved.ParseIP), [], []).
Proof.
  idtac "running ipfilter bisimulation".
  set (rel0 := mk_init 10 IPFilter.aut UDPCombined.Parse UDPInterleaved.ParseIP).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed. *)

