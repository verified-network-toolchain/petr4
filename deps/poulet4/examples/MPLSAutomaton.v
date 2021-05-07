Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import Poulet4.Bitwise.


Require Import Poulet4.P4cub.Value.
Require Import Poulet4.P4cub.P4Field.

Require Import Poulet4.P4automata.P4automaton.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Import Val.


Definition to_val (w: positive) (bs: list bool) : v :=
  let v := to_nat bs in
  VBit w (Z.of_nat v).

Definition slice {A} to from (l: list A) := firstn (from - to) (skipn to l).

Definition to_entry (bs: list bool) : v := 
  let entries := 
    ("label", to_val 20 (slice 0 20 bs)) :: 
    ("class", to_val 3 (slice 20 23 bs)) :: 
    ("bos_marker", to_val 1 (slice 23 24 bs)) ::
    ("ttl", to_val 8 (slice 24 32 bs)) ::
    nil in
  VHeader entries true.

Module MPLSSimple.
  Inductive states :=
  | parse_entry.

  Definition size' (s: states) : nat :=
    match s with
    | parse_entry => 32
    end.

  Record store := mkStore {
    entries : list v;
    length : nat;
  }.

  Instance etaStore : Settable _ := settable! mkStore <entries; length >.

  Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) => v 
      <| entries ::= fun x => x ++ [(to_entry bs)] |> 
      <| length ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) =>
      if v.(length) <? 3
      then inl parse_entry 
      else inr false
  |}.

End MPLSSimple.

Module MPLSFixedWidth.
  Inductive states :=
  | parse_entry.

  Definition size' (s: states) : nat :=
    match s with
    | parse_entry => 32
    end.

  Record store := mkStore {
    entries : list v;
    length : nat;
    seen : nat;
  }.

  Instance etaStore : Settable _ := settable! mkStore <entries; length; seen >.

  Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) =>
      match nth_error v.(entries) v.(length) with 
      | Some (VHeader fs true) => 
        match Field.get "bos_marker" fs with
        | Some (VBit _ 0) => 
          v <| entries ::= fun x => x ++ [(to_entry bs)] |> 
            <| length ::= fun x => x + 1 |> 
        | _ => v
        end
      | _ => v
      end 
      <| seen ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) => 
      if v.(seen) <? 3 
      then inl parse_entry
      else inr false
  |}.

End MPLSFixedWidth.

Module MPLSVectorized.
  Inductive states :=
  | parse_entries.

  Definition size' (s: states) : nat :=
    match s with
    | parse_entry => 32 * 4
    end.

  Record store := mkStore {
    entries : list v;
    length : nat;
  }.

  Instance etaStore : Settable _ := settable! mkStore <entries; length >.

  Definition bos_mark (entry: v) := 
    match entry with
    | VHeader fs true => 
      match Field.get "bos_marker" fs with
      | Some (VBit _ 0) => Some false
      | Some (VBit _ 1) => Some true
      | _ => None
      end
    | _ => None
    end.
  
  Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) =>
      let v1 := to_entry (slice 0 32 bs) in 
      let v2 := to_entry (slice 32 (32*2) bs) in 
      let v3 := to_entry (slice (32*2) (32*3) bs) in 
      let v4 := to_entry (slice (32*3) (32*4) bs) in
      match bos_mark v1, bos_mark v2, bos_mark v3, bos_mark v4 with
      | Some true, _, _, _ => 
        v <| entries := [v1] |> <| length := 1 |>
      | Some false, Some true, _, _ => 
        v <| entries := [v1; v2] |> <| length := 2 |>
      | Some false, Some false, Some true, _ => 
        v <| entries := [v1; v2; v3] |> <| length := 3 |>
      | Some false, Some false, Some false, Some true => 
        v <| entries := [v1; v2; v3; v4] |> <| length := 4 |>
      | _, _, _, _ => v
      end;
    transitions := fun _ _ => inr false
  |}.

End MPLSVectorized.

Require Import Poulet4.Examples.P4AutomatonValues.

Inductive fixed_vector : 
  configuration MPLSFixedWidth.parser ->
  configuration MPLSVectorized.parser ->
  Prop :=
  | Start : 
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      store_top
      store_top
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' => length buf < 32 /\ buf = buf')
      fixed_vector
  | SeenOne : 
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      (fun s => MPLSFixedWidth.seen s = 1)
      store_top
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' => 
        length buf < 32 /\ 
        exists pref,
          buf' = pref ++ buf /\
          length pref = 32
      )
      fixed_vector
  | SeenTwo : 
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      (fun s => MPLSFixedWidth.seen s = 2)
      store_top
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' => 
        length buf < 32 /\ 
        exists pref,
          buf' = pref ++ buf /\
          length pref = 32*2
      )
      fixed_vector
  | SeenThree : 
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      (fun s => MPLSFixedWidth.seen s = 3)
      store_top
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' => 
        length buf < 32 /\ 
        exists pref,
          buf' = pref ++ buf /\
          length pref = 32*3
      )
      fixed_vector.

(* TODO: remainder of this bisimulation *)
    

Example fixed_vector_bis : bisimulation fixed_vector.
Admitted.