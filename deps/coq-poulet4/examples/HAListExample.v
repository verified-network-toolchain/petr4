Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.
Require Import HAList.
Require Import Coq.Strings.String.
Open Scope string_scope.
Instance StrEqDec:EqDec string eq.
unfold EqDec.
apply string_dec.
Defined.
Set Universe Polymorphism.

Definition std_t : signature string :=
  [("src", nat); ("dst", nat)].

Definition std_example : t string std_t :=
  (0, (1, tt)).

Definition src_valid : alist_In _ "src" std_t :=
  I.

Definition lookup_src: nat :=
  HAList.get string std_example (exist _ "src" I).

Definition lookup_dst: nat :=
  HAList.get string std_example (exist _ "dst" I).

Time Eval cbv in fst std_example.       (* 0 *)
Time Eval cbv in lookup_src.            (* 0 *)
Time Eval cbv in fst (snd std_example). (* 0 *)
Time Eval cbv in lookup_dst.            (* 1 *)
