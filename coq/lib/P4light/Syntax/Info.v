Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Inductive Info : Type :=
(* info *)
| I (filename: string) (line_start: Z) (line_end: option Z) (col_start: Z)
    (col_end: Z)
(* missing info *)
| M (msg: string).

Definition dummy := M "".
