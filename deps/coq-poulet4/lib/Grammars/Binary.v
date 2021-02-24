Require Import Ascii.
Require Import Lists.List.

Require Import Grammar.
Require Import Lib.
Require Import Vector.
Import List.ListNotations.

Open Scope list_scope.

Definition binDigit : grammar nat := gsum [
  glit true @ (fun _ => 0);
  glit false @ (fun _ => 1)
].

Definition gbin := gplus binDigit @ (fun ds => List.fold_left (fun a x => 2*a + x) ds 0).

Definition gbin_n (n: nat) := repeat n binDigit @ (fun ds => Vector.fold_left (fun a x => 2*a + x) 0 ds).
