Set Warnings "-custom-entry-overridden".
From Poulet4 Require Import
     P4light.Syntax.P4defs Monads.Result
     Compile.ToP4cubTest GCL.GCL GCL.ToGCL.
Import Result ResultNotations Syntax List ListNotations.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stmt.

Definition asm_eq (s : string) (w : nat) (r : BV.t) : ToGCL.target :=
  G.GAssume (F.bveq (BV.BVVar s w) r).

Open Scope string_scope.
Definition matchrow_inner (table : string) (n : nat) (elt : nat * BV.t * E.matchkind) (acc_res : result F.t) : result F.t :=
  let (te, mk) := elt in
  let (w, k) := te in
  let symbmatch := "_symb$" ++ table ++ "$match__" ++ string_of_nat n in
  let* acc := acc_res in
  ok (F.land (F.bveq (BV.BVVar symbmatch w) k) acc).

Definition matchrow (table : string) (keys : list (nat * BV.t * E.matchkind)) : result F.t :=
  fold_lefti (matchrow_inner table) (ok (F.LBool true)) keys.

Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
  let n := List.length l in
  Nat.max (PeanoNat.Nat.log2_up n) 1.

Definition action_inner (table : string) (keys : list (nat * BV.t * E.matchkind)) (w : nat) (n : nat) (named_action : string * ToGCL.target) (res_acc : result (ToGCL.target)) : result ToGCL.target :=
  let (name, act) := named_action in
  let+ acc := res_acc in
  G.GChoice
      (G.GSeq
        (asm_eq ("_symb$" ++ table ++ "$action") w  (BV.bit (Some w) n))
        act)
      acc.

Definition actions_encoding (table : string) (keys : list (nat * BV.t * E.matchkind)) (actions : list (string * ToGCL.target)) : result ToGCL.target :=
  let w := bits_to_encode_list_index actions in
  fold_lefti (action_inner table keys w) (ok (G.GAssume (F.LBool false))) actions.

Definition instr (table : string) (i : Info) (keys: list (nat * BV.t * E.matchkind)) (actions: list (string * ToGCL.target)) : result ToGCL.target :=
  let* matchcond := matchrow table keys in
  let+ acts := actions_encoding table keys actions in
  G.GSeq (G.GAssume matchcond) acts.
