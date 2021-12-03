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
Definition d := NoInfo.

Definition asm_eq (s : string) (w : nat) (r : BV.t Info) (i : Info) : ToGCL.target Info :=
  G.GAssume _ (F.bvule _ (BV.BVVar _ s w i) r i).

Open Scope string_scope.
Definition matchrow_inner (table : string) (i : Info) (n : nat) (elt : nat * BV.t Info * E.matchkind) (acc_res : result (F.t _)) : result (F.t _) :=
  let (te, mk) := elt in
  let (w, k) := te in
  let symbmatch := "_symb_" ++ table ++ "_match__" ++ string_of_nat n in
  let* acc := acc_res in
  match mk with
  | E.MKExact =>
    ok (F.land _ (F.bvule _ (BV.BVVar _ symbmatch w i) k i) acc i)
  | E.MKTernary =>
    let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
    ok (F.land _ (F.bvule _ (BV.band _ (BV.BVVar _ symbmask w i) (BV.BVVar _ symbmatch w i) i)
                                (BV.band _ (BV.BVVar _ symbmask w i) k i) i)
                  acc i)
  | E.MKLpm =>
    let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
    ok (F.land _ (F.bvule _ (BV.band _ (BV.BVVar _ symbmask w i) (BV.BVVar _ symbmatch w i) i)
                                (BV.band _ (BV.BVVar _ symbmask w i) k i) i)
                  acc i)
  end.

Definition matchrow (table : string) (keys : list (nat * BV.t Info * E.matchkind)) (i : Info) : result (F.t _) :=
  fold_lefti (matchrow_inner table i) (ok (F.LBool _ true i)) keys.

Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
  let n := List.length l in
  Nat.max (PeanoNat.Nat.log2_up n) 1.

Definition action_inner (table : string) (i : Info) (keys : list (nat * BV.t Info * E.matchkind)) (w : nat) (n : nat) (named_action : string * ToGCL.target Info) (res_acc : result (ToGCL.target Info)) : result (ToGCL.target Info) :=
  let (name, act) := named_action in
  let* matchcond := matchrow table keys i in
  let+ acc := res_acc in
  G.g_sequence Info i
                 [G.GAssume _ matchcond;
                 asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.bit _ 1 1 i) i;
                 asm_eq ("__symb_" ++ name ++ "_action") w  (BV.bit _ w n i) i;
                 act (* TODO something with action data *)].


Definition actions_encoding (table : string) (i : Info) (keys : list (nat * BV.t Info * E.matchkind)) (actions : list (string * ToGCL.target Info)) : result (ToGCL.target Info)  :=
  let w := bits_to_encode_list_index actions in
  fold_lefti (action_inner table i keys w) (ok (G.GSkip _ i)) actions.


Definition instr (name : string) (i : Info) (keys: list (nat * BV.t Info * E.matchkind)) (actions: list (string * ToGCL.target Info)) : result (ToGCL.target Info) :=
  let+ hit := actions_encoding name i keys actions in
  let miss := asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.bit _ 1 1 i) i in
  G.GChoice _ hit miss.
