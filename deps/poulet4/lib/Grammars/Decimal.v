Require Import Ascii.
Require Import Lists.List.
Import List.ListNotations.
Require Import Grammar.
Require Import String.
Require Import Lib.

Open Scope list_scope.

Definition dec_char : grammar ascii := gsum [
  glit "1";
  glit "2";
  glit "3";
  glit "4";
  glit "5";
  glit "6";
  glit "7";
  glit "8";
  glit "9";
  glit "0" 
].

Definition dec_digit : grammar nat := gsum [
  glit "1" @ (fun _ => 1);
  glit "2" @ (fun _ => 2);
  glit "3" @ (fun _ => 3);
  glit "4" @ (fun _ => 4);
  glit "5" @ (fun _ => 5);
  glit "6" @ (fun _ => 6);
  glit "7" @ (fun _ => 7);
  glit "8" @ (fun _ => 8);
  glit "9" @ (fun _ => 9);
  glit "0" @ (fun _ => 0) 
].

Definition digs_to_num (ds: list nat) : nat := fold_left (fun a x => 10*a + x) ds 0.

Definition gdec := gplus dec_digit @ digs_to_num.

Definition gdec_bounded (num_digs: nat) := 
  gprod (fun a x => 10*a + x) (List.repeat dec_digit num_digs) 0.
