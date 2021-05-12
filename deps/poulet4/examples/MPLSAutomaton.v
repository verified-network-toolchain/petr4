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

  Program Definition parser : p4automaton := {|
    size := size';
    update := fun s bs (v: store) => v
      <| entries ::= fun x => x ++ [(to_entry bs)] |>
      <| length ::= fun x => x + 1 |> ;
    transitions := fun _ (v: store) =>
      if v.(length) <? 3
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
      if v.(seen) <? 3
      then inl parse_entry
      else inr (v.(seen) =? 3)
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

  Check states_cap.

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
    transitions := fun _ _ => inr false;
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
      (fun buf buf' => length buf < 32 /\ buf = buf')
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

Example fixed_vector_bis : bisimulation fixed_vector.
  unfold bisimulation.
  intros.
  inversion H; split; intros.
  - split; intros; unfold accepting in *; exfalso; inversion H5.
  - unfold step.
    destruct H2.
    rewrite <- H5.
    simpl size. unfold MPLSVectorized.size'.
    destruct (equiv_dec _ _); destruct (equiv_dec _ _).
    + exfalso. unfold "===" in *. lia.
    + simpl transitions.
      destruct H0 as [HL0 [HL1 HL2]].
      rewrite HL1, HL2.
      simpl.
      rewrite HL0.
      simpl.
      rewrite HL1, HL2.
      simpl.

      eapply SeenOne.

      * simpl. lia.
      * compute. trivial.
      * split; [compute; lia|].
          exists (buf1 ++ [b]). 
          split; [|unfold "===" in *; trivial].
          rewrite app_nil_r.
          trivial.
    + exfalso. unfold "===" in e. 
      erewrite app_length in e.
      simpl in e. 
      lia.
    + eapply Start; trivial.
      split; trivial.
      unfold "=/=" in c.
      erewrite app_length in *.
      simpl in c. simpl.
      unfold "<".
      unfold "===" in c.
      lia.
  - split; intros; unfold accepting in *; exfalso; inversion H5.
  - unfold step.
    destruct H2 as [H2 [pref [HP HPL]]].
    destruct (equiv_dec _ _); destruct (equiv_dec _ _).
    + simpl in e. 
      simpl in e0.
      unfold MPLSVectorized.size' in e0.
      exfalso. 
      unfold "===" in *.
      erewrite app_length in *.
      rewrite HP in e0.
      erewrite app_length in e0.
      lia.
    + simpl in e, c. unfold MPLSVectorized.size' in c.
      simpl transitions.
      destruct (nth_error _ _).
      * destruct v0.
        6: {
          destruct validity.
          1 : {
            destruct (Field.get _ _).
            1: {
              destruct v0.
              3: {
                destruct n;
                simpl MPLSFixedWidth.seen;
                rewrite H0;
                simpl; 
                destruct (nth_error _ _).
                2,4,6: (
                  eapply SeenTwo
                ); simpl MPLSFixedWidth.seen; try rewrite H0; auto.

                2,3,4: (
                  split; [simpl; lia|];
                  exists (buf2 ++ [b]);
                  split; [rewrite app_nil_r; trivial|];
                  rewrite HP; 
                  rewrite <- app_assoc; 
                  rewrite app_length; 
                  rewrite e;
                  rewrite HPL;
                  auto 
                ).
                all: (
                  destruct v0; try apply SeenTwo;
                  simpl MPLSFixedWidth.seen; try rewrite H0; auto;
                  try (
                    split; [simpl; lia|];
                    exists (buf2 ++ [b]);
                    split; [rewrite app_nil_r; trivial|];
                    rewrite HP; 
                    rewrite <- app_assoc; 
                    rewrite app_length; 
                    rewrite e;
                    rewrite HPL;
                    auto 
                  );
                  destruct validity; [|rewrite H0; trivial];
                  destruct (Field.get _ _); [|rewrite H0; trivial];
                  destruct v0; (
                    rewrite H0; trivial
                  ) || (
                    destruct n; 
                    simpl MPLSFixedWidth.seen;
                    rewrite H0; 
                    trivial
                  )
                ).
              }
              all : (
                rewrite H0;
                simpl;
                destruct (nth_error _ _) ;
                (
                  eapply SeenTwo;
                  simpl MPLSFixedWidth.seen; try rewrite H0; auto;
                  split; [simpl; lia|];
                  exists (buf2 ++ [b]);
                  split; [rewrite app_nil_r; trivial|];
                  rewrite HP; 
                  rewrite <- app_assoc; 
                  rewrite app_length; 
                  rewrite e;
                  rewrite HPL;
                  auto 
                ) || (
                  destruct v0; try apply SeenTwo;
                  simpl MPLSFixedWidth.seen; try rewrite H0; auto;
                  try (
                    split; [simpl; lia|];
                    exists (buf2 ++ [b]);
                    split; [rewrite app_nil_r; trivial|];
                    rewrite HP; 
                    rewrite <- app_assoc; 
                    rewrite app_length; 
                    rewrite e;
                    rewrite HPL;
                    auto 
                  );
                  
                  destruct validity; (
                    rewrite H0; trivial
                  ) || (
                    destruct (Field.get _ _); (
                      rewrite H0; trivial
                    ) || (
                      destruct v0; (
                        rewrite H0; trivial
                      ) || (
                        destruct n; 
                        simpl MPLSFixedWidth.seen;
                        rewrite H0; 
                        trivial 
                      )
                    ) || (
                      destruct v0; (
                        rewrite H0; trivial
                      ) || (
                        destruct n0; 
                        simpl MPLSFixedWidth.seen;
                        rewrite H0; 
                        trivial 
                      )
                    ) || (
                      destruct validity0; (
                        destruct v0; (
                          rewrite H0; trivial
                        ) || (
                          destruct n; 
                          simpl MPLSFixedWidth.seen;
                          rewrite H0; 
                          trivial 
                        )
                      ) || (
                        rewrite H0; trivial
                      )
                    )
                  )
                )
              ).
            }
            rewrite H0.
            simpl.

            destruct (nth_error _ _) ;
            eapply SeenTwo;
            auto.
            2, 4: (
              split; [simpl; lia|];
              exists (buf2 ++ [b]);
              split; [rewrite app_nil_r; trivial|];
              rewrite HP; 
              rewrite <- app_assoc; 
              rewrite app_length; 
              rewrite e;
              rewrite HPL;
              auto 
            ).
            1: {
              destruct v0.
              6: {
                destruct validity; [|simpl; rewrite H0; auto].
                destruct (Field.get _ _); [|simpl; rewrite H0; auto].
                destruct v0.
                3: {
                  destruct n;
                  simpl; rewrite H0; auto.
                }
                all: (
                  simpl; rewrite H0; auto
                ).
              }
              all : ( simpl; rewrite H0; auto).
            }
            destruct sig1.
            simpl in H0.
            rewrite H0. auto.
          }
          rewrite H0.
          simpl.

          destruct (nth_error _ _); [| 
            eapply SeenTwo;
            auto; [
              destruct sig1; simpl in H0; rewrite H0; auto | 
              split; [
                simpl; lia | 
                exists (buf2 ++ [b]);
                split; [rewrite app_nil_r; trivial|];
                rewrite HP; 
                rewrite <- app_assoc; 
                rewrite app_length; 
                rewrite e;
                rewrite HPL;
                auto 
              ]
            ]
          ].
          
          destruct v0.
          6: (
            destruct validity;
            try destruct (Field.get _ _);
            try destruct v0;
            try destruct n
          ).
          all: (
            eapply SeenTwo;
            auto; [
              destruct sig1; simpl in H0; rewrite H0; auto | 
              split; [
                simpl; lia | 
                exists (buf2 ++ [b]);
                split; [rewrite app_nil_r; trivial|];
                rewrite HP; 
                rewrite <- app_assoc; 
                rewrite app_length; 
                rewrite e;
                rewrite HPL;
                auto 
              ]
            ]
          ).
          
        }
        all: rewrite H0; simpl.
        1,4,5,6,7,8: (
          destruct (nth_error _ _); (
            destruct v0; eapply SeenTwo; auto;
            try (inversion H0; simpl; rewrite H0; auto);
            try (
              split; [
                lia | 
                exists (buf2 ++ [b]); split; [
                  rewrite app_nil_r; trivial |
                ]
              ];
              rewrite HP;
              rewrite <- app_assoc;
              rewrite app_length;
              rewrite e;
              lia
            );

            destruct validity; [|rewrite H6; auto];
            destruct (Field.get _ _); [| rewrite H6; auto];
            destruct v0; try rewrite H6; auto;
            destruct n; try rewrite H6; auto;
            simpl;
            rewrite H6;
            auto 
            ) || (
              eapply SeenTwo;
              (compute; destruct sig1; simpl in H0; rewrite H0; trivial) ||
              auto ||
              split;
              (compute; lia) || (
              exists (buf2 ++ [b]);
              split; (
                try rewrite app_nil_r; trivial || 
                rewrite HP; 
                rewrite <- app_assoc; 
                rewrite app_length; 
                rewrite e;
                rewrite HPL;
                auto 
                )
              )
            )
          ).

          1: {
            destruct (nth_error _ _).
            destruct v0;
            eapply SeenTwo;
            auto;
            destruct sig1; 
            simpl in H0;
            try rewrite H0;
            auto;
            try (
              split;
              simpl;
              try lia
            );
            try (
              exists (buf2 ++ [b]);
              split;
              try rewrite app_nil_r; trivial ;
              rewrite HP; 
              rewrite <- app_assoc; 
              rewrite app_length; 
              rewrite e;
              rewrite HPL;
              auto 
            ); try (
              destruct validity; simpl; trivial;
              destruct (Field.get _ _); simpl; trivial;
              destruct v0;
              try destruct n0;
              auto
            ).

            eapply SeenTwo; destruct sig1;
            simpl in H0; try rewrite H0;
            simpl; auto.

            split; [lia|].

            exists (buf2 ++ [b]).
            split;
            try rewrite app_nil_r; trivial ;
            rewrite HP; 
            rewrite <- app_assoc; 
            rewrite app_length; 
            rewrite e;
            rewrite HPL;
            auto.
          }

          (* This is copy-paste from above, TODO refactor *)

          1: {
            destruct (nth_error _ _).
            destruct v0;
            eapply SeenTwo;
            auto;
            destruct sig1; 
            simpl in H0;
            try rewrite H0;
            auto;
            try (
              split;
              simpl;
              try lia
            );
            try (
              exists (buf2 ++ [b]);
              split;
              try rewrite app_nil_r; trivial ;
              rewrite HP; 
              rewrite <- app_assoc; 
              rewrite app_length; 
              rewrite e;
              rewrite HPL;
              auto 
            ); try (
              destruct validity; simpl; trivial;
              destruct (Field.get _ _); simpl; trivial;
              destruct v0;
              try destruct n0;
              auto
            ).

            eapply SeenTwo; destruct sig1;
            simpl in H0; try rewrite H0;
            simpl; auto.

            split; [lia|].

            exists (buf2 ++ [b]).
            split;
            try rewrite app_nil_r; trivial ;
            rewrite HP; 
            rewrite <- app_assoc; 
            rewrite app_length; 
            rewrite e;
            rewrite HPL;
            auto.
          }
        
      * simpl MPLSFixedWidth.seen.
        rewrite H0.
        simpl.
        destruct (nth_error _ _).
        destruct v0.
        6: {
          destruct validity.
          1 : {
            destruct (Field.get _ _).
            1: (
              destruct v0;
              try destruct n;
              try simpl MPLSFixedWidth.seen
            ).
            all: (
              eapply SeenTwo;
              auto;
              simpl MPLSFixedWidth.seen;
              try rewrite H0; auto;
              split; [simpl; lia|];
              exists (buf2 ++ [b]);
              split; [rewrite app_nil_r; trivial|];
              rewrite HP; 
              rewrite <- app_assoc; 
              rewrite app_length; 
              rewrite e;
              rewrite HPL;
              auto 
            ).
          }
          
          eapply SeenTwo;
          auto;
          simpl MPLSFixedWidth.seen;
          try rewrite H0; auto;
          split; [simpl; lia|];
          exists (buf2 ++ [b]);
          split; [rewrite app_nil_r; trivial|];
          rewrite HP; 
          rewrite <- app_assoc; 
          rewrite app_length; 
          rewrite e;
          rewrite HPL;
          auto.
            
        }

        all: (
          eapply SeenTwo;
          auto;
          simpl MPLSFixedWidth.seen;
          try rewrite H0; auto;
          split; [simpl; lia|];
          exists (buf2 ++ [b]);
          split; [rewrite app_nil_r; trivial|];
          rewrite HP; 
          rewrite <- app_assoc; 
          rewrite app_length; 
          rewrite e;
          rewrite HPL;
          auto 
        ).
    
    + exfalso.
      simpl in c, e.
      unfold MPLSVectorized.size' in e.
      rewrite HP in e.
      repeat (rewrite app_length in e).
      rewrite HPL in e.
      inversion e.
      lia.
    + simpl in c, c0.
      unfold MPLSVectorized.size' in c0.
      eapply SeenOne; auto.
      split; [rewrite app_length in *; simpl in * |].
      * unfold "=/=" in c.
          unfold "===" in c.
          lia.
      * exists pref.
        split; trivial.
        rewrite HP.
        rewrite <- app_assoc.
        trivial.
  - split; intros; exfalso; inversion H5.
  - simpl step.
    destruct (equiv_dec _ _).
    + destruct (nth_error _ _).
      * admit.
      * simpl; rewrite H0; simpl.
        admit.
    + admit.

  - split; intros; exfalso; inversion H5.
  - admit.
  - split; intros; inversion H5; unfold accepting; trivial.
  - eapply EndStates; auto; rewrite H2; trivial.
Admitted.
