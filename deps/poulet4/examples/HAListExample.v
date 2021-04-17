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

Definition std_example : t std_t :=
  RCons 10 (RCons 16 REmp).

Definition src_valid : alist_In "src" std_t :=
  I.

Definition lookup_src: nat :=
  HAList.get std_example (exist _ "src" I).

Definition lookup_dst: nat :=
  HAList.get std_example (exist _ "dst" I).

Definition update_dst: t std_t :=
  HAList.set std_example (exist _ "dst" I) 22.

Lemma update_dst_eval :
  update_dst = RCons 10 (RCons 22 REmp).
Proof.
  reflexivity.
Qed.
