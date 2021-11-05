Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Require Import Poulet4.Bitwise.


Require Import Poulet4.P4cub.BigStep.Value.
Require Import Poulet4.P4cub.Syntax.P4Field.

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

  Program Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) => v
      <| entries ::= fun x => x ++ [(to_entry bs)] |>
      <| length ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) =>
      if v.(length) <? 4
      then inl parse_entry
      else inr false
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

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

  Program Definition parser : p4automaton := {|
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
      | Some _ => v
      | None => v <| entries := [to_entry bs] |> <| length := 1 |>
      end
      <| seen ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) =>
      if v.(seen) <? 4
      then inl parse_entry
      else inr (v.(seen) =? 4)
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

End MPLSFixedWidth.

Module MPLSVectorized.
  Inductive states :=
  | parse_entries.

  Definition size' (s: states) : nat :=
    match s with
    | parse_entries => 32 * 4
    end.

  Lemma states_cap:
    forall s,
      0 < size' s
  .
  Proof.
    destruct s; simpl; lia.
  Qed.

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
    transitions := fun _ _ => inr true;
    cap := states_cap;
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
      (fun s =>
        s.(MPLSFixedWidth.seen) = 0 /\
        s.(MPLSFixedWidth.length) = 0 /\
        s.(MPLSFixedWidth.entries) = nil
      )
      (fun s =>
        s.(MPLSVectorized.length) = 0 /\
        s.(MPLSVectorized.entries) = nil
      )
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' => buf = nil /\ buf = buf')
      fixed_vector
  | SeenOne :
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      (fun s => s.(MPLSFixedWidth.seen) = 1)
      store_top
      (inl MPLSFixedWidth.parse_entry)
      (inl MPLSVectorized.parse_entries)
      (fun buf buf' =>
        buf = nil /\
        length buf' = 32
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
        buf = nil /\
        length buf' = 32 * 2
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
        buf = nil /\
        length buf' = 32 * 3
      )
      fixed_vector
  | EndStates :
    forall b,
    build_bisimulation
      (a1 := MPLSFixedWidth.parser)
      (a2 := MPLSVectorized.parser)
      store_top
      store_top
      (inr b)
      (inr b)
      (fun buf buf' => buf = buf')
      fixed_vector.

Ltac length_contra' := 
  exfalso; 
  unfold "===" in *; 
  repeat (
    match goal with 
    | [H : ?L = ?R ++ _ |- _ ] => rewrite H in *
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _, _ |- _ ] => destruct H
    end
  );
  repeat (rewrite app_length in *);
  simpl in *.

Ltac length_contra := 
  (length_contra'; congruence || lia) || (
    match goal with 
    | [ H : _ -> False |- False ] => eapply H; lia
    end
  ).

Ltac state_contra := 
  split; intros; unfold accepting in *; simpl in *; congruence.

Ltac mysimp :=
  repeat (
    match goal with 
    | [H : ?L = ?R ++ _ |- _ ] => rewrite H in *
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _, _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    end
  );
  unfold store_top in *;
  try repeat (rewrite app_length in *);
  unfold "===" in *;
  unfold "=/=" in *; 
  simpl in *; lia || auto.

Ltac solve_prefix :=
  match goal with 
  | [ |- exists X, ?L = X ++ nil /\ _ ] => exists L; split; [rewrite app_nil_r; trivial |]
  | [ |- exists X, (?L ++ ?R) ++ ?B = X ++ ?R ++ ?B /\ _ ] => exists L; split; [rewrite app_assoc; trivial |] 
  end.

Ltac break_matches :=
  match goal with 
  | [ |- context[ nth_error _ _ ]] => destruct (nth_error _ _)
  | [ |- context[ match ?X with | VBool _ => _ | _ => _ end ]] => destruct X
  | [ |- context[ Field.get _ _ ]] => destruct (Field.get _ _)
  | [ |- context[ match ?X with 0%Z => _ | _ => _ end ]] => destruct X
  | [ |- context[ match ?X with 1%positive => _ | _ => _ end ]] => destruct X
  | [ H: ?X = ?Y |- context[ ?X + _ ]] => rewrite H; simpl
  | [ |- context[ if ?X <? ?Y then _ else _ ]] => destruct (X <? Y) eqn:?
  | [ |- context[ if ?X then _ else _ ]] => destruct X
  end.


Lemma add_1: 
  forall n, n + 1 = S n.
Proof.
  intros. induction n; auto.
  rewrite Nat.add_succ_l.
  rewrite <- IHn.
  trivial.
Qed.

Ltac seen_solver := 
  simpl; auto; 
  repeat (break_matches || mysimp; (lia || solve_prefix || auto));
  mysimp; (lia || auto).

Ltac seen_solver' :=
  constructor; now seen_solver.

Lemma min_same : 
  forall n, min n n = n.
Proof.
  intros.
  induction n; auto.
  unfold min.
  fold min.
  rewrite IHn.
  trivial.
Qed.


Example fixed_vector_bis : bisimulation_with_leaps fixed_vector.
  unfold bisimulation_with_leaps.
  intros.
  inversion H; clear H; split; intros; try state_contra.
  - destruct H2.
    rewrite <- H5 in *.
    rewrite H2 in *.
    simpl in H.
    rewrite (@follow_exact MPLSFixedWidth.parser); [|mysimp|mysimp].
    rewrite (@follow_buffer MPLSVectorized.parser); [|mysimp].
    do 32 (destruct buf; [exfalso; inversion H|]).
    destruct buf; [| exfalso; simpl in H; inversion H].
    clear H.
    simpl.
    destruct H0.
    destruct H0.
    repeat break_matches; (
      (exfalso;
      simpl in *;
        (rewrite H in *) || (rewrite H0 in *); 
        simpl in *;
      now inversion Heqb32 || now inversion Heqb31
      ) ||
      seen_solver'
    ).
  - destruct H2.
    rewrite H2 in *.
    simpl in H.
    rewrite H5 in H.
    simpl in H.
    rewrite (@follow_exact MPLSFixedWidth.parser); [|mysimp|mysimp].
    rewrite (@follow_buffer MPLSVectorized.parser); [|mysimp].
    do 32 (destruct buf; [exfalso; inversion H|]).
    destruct buf; [| exfalso; simpl in H; inversion H].
    clear H.
    simpl.
    repeat break_matches; (
      (exfalso;
      simpl in *;
        (rewrite H in *) || (rewrite H0 in *); 
        simpl in *;
      now inversion Heqb32 || now inversion Heqb31
      ) ||
      seen_solver'
    ).
  - destruct H2.
    rewrite H2 in *.
    simpl in H.
    rewrite H5 in H.
    simpl in H.
    rewrite (@follow_exact MPLSFixedWidth.parser); [|mysimp|mysimp].
    rewrite (@follow_buffer MPLSVectorized.parser); [|mysimp].
    do 32 (destruct buf; [exfalso; inversion H|]).
    destruct buf; [| exfalso; simpl in H; inversion H].
    clear H.
    simpl.
    repeat break_matches; (
      (exfalso;
      simpl in *;
        (rewrite H in *) || (rewrite H0 in *); 
        simpl in *;
      now inversion Heqb32 || now inversion Heqb31
      ) ||
      seen_solver'
    ).
  - destruct H2.
    rewrite H2 in *.
    simpl in H.
    rewrite H5 in H.
    simpl in H.
    rewrite (@follow_exact MPLSFixedWidth.parser); [|mysimp|mysimp].
    rewrite (@follow_exact MPLSVectorized.parser); [|mysimp|mysimp].
    do 32 (destruct buf; [exfalso; inversion H|]).
    destruct buf; [| exfalso; simpl in H; inversion H].
    clear H.
    simpl.
    destruct sig1.
    simpl in *.
    rewrite H0 in *.
    simpl in *.
    do 96 (destruct buf2; [exfalso; inversion H5|]).
    destruct buf2; [|exfalso; inversion H5].
    clear H5.
    repeat (
      seen_solver' || 
      unfold MPLSAutomaton.slice; simpl; break_matches
    ); (
      now (exfalso; inversion Heqb128 || inversion Heqb127)
    ).
    

  - simpl in H.
    destruct buf; [exfalso; inversion H|].
    destruct buf; [|exfalso; inversion H].
    clear H.
    rewrite H2 in *.
    destruct buf2.
    cbv.
    + simpl.
      seen_solver'.
    + simpl.
      rewrite app_length.
      rewrite plus_comm.
      simpl.
      seen_solver'.
Qed.
