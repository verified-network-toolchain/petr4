Set Warnings "-custom-entry-overridden".
From Poulet4 Require Import
     Monads.Result GCL.GCL GCL.ToGCL.
Import Result ResultNotations Syntax List ListNotations.
Import String.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stmt.

Definition asm_eq (s : string) (w : nat) (r : BV.t) : ToGCL.target :=
  G.GAssume (F.bveq (BV.BVVar s w) r).

Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
  let n := List.length l in
  Nat.max (PeanoNat.Nat.log2_up n) 1.

Definition action_inner (table : string) (keys : list (nat * BV.t * string)) (w : nat) (n : nat) (named_action : string * ((list BV.t) * ToGCL.target)) (res_acc : result (ToGCL.target)) : result ToGCL.target :=
  let (name, act) := named_action in
  let+ acc := res_acc in
  G.GChoice
      (G.GSeq
        (asm_eq ("_symb$" ++ table ++ "$action") w  (BV.bit (Some w) n))
        (snd act))
      acc.

Definition actions_encoding (table : string) (keys : list (nat * BV.t * string)) (actions : list (string * ((list BV.t) * ToGCL.target))) : result ToGCL.target :=
  let w := bits_to_encode_list_index actions in
  fold_lefti (action_inner table keys w) (ok (G.GAssume (F.LBool false))) actions.

Definition instr {tags_t : Type} (table : string) (keys: list (nat * BV.t * string)) (actions: list (string * ((list BV.t) * ToGCL.target))) : result ToGCL.target :=
  let+ acts := actions_encoding table keys actions in
  acts.
