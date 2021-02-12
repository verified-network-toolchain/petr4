Require Import Ascii.

Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Vector.

Definition bit := glitr "1" true <|> glitr "0" false.

Definition bits (n: nat) : Set := prod bool n.

Definition bits_n (n : nat) : grammar (bits n) := repeat_prod n bit.