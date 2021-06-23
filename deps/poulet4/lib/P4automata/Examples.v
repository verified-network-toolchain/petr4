Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Module Simple.
  Inductive state :=
  | Start.

  Inductive header :=
  | HdrSimple.

  Definition st_start: Syntax.state state header :=
    {| st_op := OpExtract 16 (HRVar HdrSimple);
       st_trans := TGoto _ (inr true) |}.

  Definition aut: Syntax.t state header :=
    Env.bind Start st_start (Env.empty _ _).
End Simple. 

Module Split.
  Inductive state :=
  | StSplit1
  | StSplit2.

  Inductive header :=
  | HdrSplit1
  | HdrSplit2.

  Definition st_split1: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit1);
       st_trans := TGoto _ (inl StSplit2) |}.

  Definition st_split2: Syntax.state state header :=
    {| st_op := OpExtract 8 (HRVar HdrSplit2);
       st_trans := TGoto _ (inr true) |}.

  Definition aut: Syntax.t state header :=
    Env.bind StSplit1 st_split1 (Env.bind StSplit2 st_split2 (Env.empty _ _)).
End Split.

Module SimpleSplit.
  Definition aut := Eval cbv in sum Simple.aut Split.aut.
  Print aut.
End SimpleSplit.

