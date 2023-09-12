Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(* From Coq Require Import Numbers.BinNums Classes.EquivDec. *)
From Poulet4.Surface.Syntax Require Import Syntax.
From Poulet4.P4light.Syntax Require Import Info ConstValue.

From Poulet4.P4light.Syntax Require P4String.


Section CheckerEnv.

  Notation P4String := (P4String.t Info).
  Notation P4Value := (@Value Info). (*for now using p4light values*)
  (* Notation P4Int := (P4Int.t Info). *)

  Definition env (a : Type) := P4String.AList Info a.

  Record checkerEnvs :=
    { typeEnv: env typ;
      typeSynEnv: env P4String;
      varEnv: env (typ * direction);
      constEnv: env P4Value; (*for now using p4light values*)
      externEnv: env P4String;
    }.


End CheckerEnv. 

