Require Import Poulet4.P4defs.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.ToP4cubTest.
Require Import Poulet4.P4cub.Envn.
Require Poulet4.P4cub.GCL.
Require Poulet4.P4cub.ToGCL.
Import Result ResultNotations SimpleNat Syntax List ListNotations.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stmt.

Definition asm_eq (s : string) (w : nat) (r : BV.t) : ToGCL.target :=
  G.GAssume (F.bvule (BV.BVVar s w) r).

Open Scope string_scope.
Definition matchrow_inner (table : string) (n : nat) (elt : nat * BV.t * E.matchkind) (acc_res : result F.t) : result F.t :=
  let (te, mk) := elt in
  let (w, k) := te in
  let symbmatch := "_symb_" ++ table ++ "_match__" ++ string_of_nat n in
  let* acc := acc_res in
  match mk with
  | E.MKExact =>
    ok (F.land (F.bvule (BV.BVVar symbmatch w) k) acc)
  | E.MKTernary =>
    let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
    ok (F.land (F.bvule (BV.band (BV.BVVar symbmask w) (BV.BVVar symbmatch w))
                        (BV.band (BV.BVVar symbmask w) k))
                  acc)
  | E.MKLpm =>
    let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
    ok (F.land (F.bvule (BV.band (BV.BVVar symbmask w) (BV.BVVar symbmatch w))
                        (BV.band (BV.BVVar symbmask w) k))
               acc)
  end.

Definition matchrow (table : string) (keys : list (nat * BV.t * E.matchkind)) : result F.t :=
  fold_lefti (matchrow_inner table) (ok (F.LBool true)) keys.

Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
  let n := List.length l in
  Nat.max (PeanoNat.Nat.log2_up n) 1.

Definition action_inner (table : string) (keys : list (nat * BV.t * E.matchkind)) (w : nat) (n : nat) (named_action : string * ToGCL.target) (res_acc : result (ToGCL.target)) : result ToGCL.target :=
  let (name, act) := named_action in
  let* matchcond := matchrow table keys in
  let+ acc := res_acc in
  G.g_sequence
    [G.GAssume matchcond;
    asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.bit 1 1);
    asm_eq ("__symb_" ++ name ++ "_action") w  (BV.bit w n);
    act (* TODO something with action data *)].


Definition actions_encoding (table : string) (keys : list (nat * BV.t * E.matchkind)) (actions : list (string * ToGCL.target)) : result ToGCL.target :=
  let w := bits_to_encode_list_index actions in
  fold_lefti (action_inner table keys w) (ok (G.GSkip)) actions.


Definition instr (name : string) (i : Info) (keys: list (nat * BV.t * E.matchkind)) (actions: list (string * ToGCL.target)) : result ToGCL.target :=
  let+ hit := actions_encoding name keys actions in
  let miss := asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.bit 1 1) in
  G.GChoice hit miss.
