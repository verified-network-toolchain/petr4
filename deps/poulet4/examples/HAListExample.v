Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.

Import ListNotations.

Require Import Poulet4.HAList.

Open Scope string_scope.

Instance StrEqDec:EqDec string eq.
Proof.
  unfold EqDec.
  apply string_dec.
Defined.

Definition std_t : signature string :=
  [("src", nat); ("dst", nat)].

Definition std_example : t string std_t :=
  (10, (16, tt)).

Definition src_valid : alist_In _ "src" std_t :=
  I.

Definition lookup_src: nat :=
  HAList.get _ std_example (exist _ "src" I).

Definition lookup_dst: nat :=
  HAList.get _ std_example (exist _ "dst" I).

Time Eval cbv in fst std_example.       (* 0 *)
Time Eval cbv in lookup_src.            (* 0 *)
Time Eval cbv in fst (snd std_example). (* 0 *)
Time Eval cbv in lookup_dst.            (* 1 *)
