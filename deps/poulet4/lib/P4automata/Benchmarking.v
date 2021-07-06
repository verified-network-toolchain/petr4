Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.HAList.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.Sum.



Section Size.
Definition size_value (x: Syntax.v) := 
  match x with 
  | VBits bs => length bs
  end.

Fixpoint size_pat (p: Syntax.pat) := 
  1 + match p with 
  | PExact v => size_value v
  | PAny => 0
  | PPair l r => size_pat l + size_pat r
  end.

Fixpoint size_expr {H} (e: Syntax.expr H) := 
  1 + match e with 
  | EHdr (HRVar _) => 1
  | ELit _ bs => length bs
  | ESlice i _ _ => size_expr i
  end.

Fixpoint size_cond {H} (c: Syntax.cond H) := 
  1 + match c with  
  | CExpr e => size_expr e
  | CPair l r => size_cond l + size_cond r
  end.

Definition size_state_ref {H} (sr: Syntax.state_ref H) := 2.

Definition size_sel_case {H} (sc: Syntax.sel_case H) :=
  size_pat sc.(sc_pat) + size_state_ref sc.(sc_st).

Definition size_transition {A B} (t: Syntax.transition A B) := 
  1 + match t with 
  | TGoto _ x => size_state_ref x
  | TSel c cs def => 
    let sizes := List.map size_sel_case cs in 
    size_cond c + (List.fold_left (fun a b => a + b) sizes 0) + size_state_ref def
  end.

Fixpoint size_op {A} (o: Syntax.op A) := 
  1 + match o with 
  | OpAsgn (HRVar _) r => 1 + size_expr r
  | OpSeq l r => size_op l + size_op r
  | OpExtract w (HRVar _) => 2
  | OpNil _ => 0
  end.

Definition size_state {A B} (st: Syntax.state A B) :=
  1 + size_op st.(st_op) + size_transition st.(st_trans).


Definition size_auto {S H} {S_eq_dec: EquivDec.EqDec S eq} {S_finite: @Finite S _ _} (a: Syntax.t S H) : nat.
  destruct S_finite.
  set (states := List.map (a.(t_states)) enum).
  exact (List.fold_left (fun a b => a + b) (List.map size_state states) 0).
Defined.

End Size. 

Require Import Poulet4.P4automata.Examples.BabyIP.
Require Import Poulet4.P4automata.Examples.IPFilter.
Require Import Poulet4.P4automata.Examples.MPLSVectorized.
Require Import Poulet4.P4automata.Examples.ProofHeader.

Section Benchmarks.
  (* Eval vm_compute in (size_auto BabyIP1.aut). (* Separate *)
  Eval vm_compute in (size_auto BabyIP2.aut). (* Merged *)
  Eval vm_compute in (size_auto UDPInterleaved.aut). (* Incremental *)
  Eval vm_compute in (size_auto UDPCombined.aut). (* Postfilter *)

  Eval vm_compute in (size_auto MPLSPlain.aut). (* Plain *)
  Eval vm_compute in (size_auto MPLSUnroll.aut). (* Unrolled *)
  Eval vm_compute in (size_auto MPLSInline.aut). (* Inlined *) *)


  (* Eval vm_compute in (length ((mk_init 10 BabyIP.aut BabyIP1.Start BabyIP2.Start))).
  Eval vm_compute in (length (mk_init 10 IPFilter.aut UDPCombined.Parse UDPInterleaved.ParseIP)).
  Eval vm_compute in (length (mk_init 10 MPLSVect.aut MPLSPlain.ParseMPLS MPLSUnroll.ParseMPLS0)).
  Eval vm_compute in (length (mk_init 10 MPLSVectUnroll.aut MPLSPlain.ParseMPLS MPLSInline.ParseMPLS)). *)
End Benchmarks.