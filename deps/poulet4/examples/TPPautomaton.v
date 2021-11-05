Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Require Import Poulet4.Bitwise.

Require Import Poulet4.Monads.Option.

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

  
(* tuple of n bytes *)

Definition byte := {n: nat | n < 256 }.

Definition bits_to_nat (x: list bool) : {n: nat | n < 2^ length x}. 
induction x.
  - refine (exist _ 0 _).
    simpl.
    lia.
  - destruct IHx.
    destruct a.
    * refine (exist _ (x0 * 2) _).
      simpl.
      lia.
    * refine (exist _ x0 _).
      simpl.
      lia.
Defined.

Definition bits_8_to_byte (x: list bool) (pf: length x <= 8) : byte.
Admitted.

Lemma bits_8_pf_irrel :
  forall l pf pf', bits_8_to_byte l pf = bits_8_to_byte l pf'.
Admitted.

Fixpoint bytes (n : nat) : Type := 
  match n with 
  | 0 => unit
  | S n' => byte * bytes n'
  end.

Definition bs_idx {n} (bs: bytes (S n)) (i : nat) (pf: i <= (S n)) : byte.
induction i.
destruct bs.
- exact b.
- eapply IHi.
  lia.
Defined.

Definition slice {A} to from (l: list A) := firstn (from - to) (skipn to l).

Lemma slice_n_n' : 
  forall {A} (l : list A) n n', 
  length (slice n n' l) <= (n' - n). 
Admitted.

Fixpoint snoc {A} (x: A) (xs: list A) : list A :=
  match xs with 
  | nil       => x :: nil
  | x' :: xs' => x' :: (snoc x xs')
  end.


Module TPP.
  Inductive states :=
  | parse_ip
  | parse_udp
  | parse_tpp_header
  | parse_tpp_instr
  | parse_tpp_memory
  | parse_suffix.

  Definition size' (s: states) : nat :=
    match s with
    | parse_ip => 6*8 (* 8 bytes for src/dest, 2 for protocol *)
    | parse_udp => 2*8 (* 2 bytes for dest port *)
    | parse_tpp_header => 8*8 (* 8 bytes in total *)
    | parse_tpp_instr => 4*8 (* 4 bytes per instruction, parse byte-by-byte *)
    | parse_tpp_memory => 8 (* parse memory byte-by-byte *)
    | parse_suffix => 2*8 (* 2 byte proto trailer *)
    end.

  Record ip := mkIP {
    source : bytes 4 ;
    dest : bytes 4;
    proto: bytes 2;
  }.

  Record udp := mkUDP {
    dest_port : byte ; 
    inner_len : byte ;
  }.

  Record tpp_header := mkTPPHeader {
    instr_len : nat;
    mem_len : nat;
    addr_mode: nat;
    sp : nat;
    phmem_len : nat;
  }.

  Definition operand := byte.
  
  Inductive tpp_instr := 
  | TPPload (r: operand) (l: operand)
  | TPPstore (l: operand) (r: operand) 
  (* | TPPpush (x: operand)
  | TPPpop (x: operand) *)
  | TPPcondstore (x: operand) (x': operand) (v: operand)
  | TPPcexec (addr: operand) (mask: operand).

  Definition tpp_mem := list byte.

  Definition tpp_program := (tpp_instr * list tpp_instr)%type.

  Inductive tpp_sec_label := TSHigh | TSLow .

  Scheme Equality for tpp_sec_label.

  Definition tsed := tpp_sec_label_eq_dec.
  
  Definition sec_typ_env := operand -> tpp_sec_label.

  Definition tpp_check_instr (env: sec_typ_env) (i: tpp_instr) := 
    match i with 
    | TPPload r l
    | TPPstore l r 
    | TPPcexec l r =>
      if tsed (env l) (env r) then Some (env l) else None
    (* | TPPpush x
    | TPPpop x => 
      if tsed (env x) (env sp) then Some (env x) else None *)
    | TPPcondstore x x' v => 
      if tsed (env x) (env x') 
      then if tsed (env x') (env v) 
      then Some (env x) else None
      else None
    end.
  
  Program Fixpoint tpp_check_prog (env: sec_typ_env) (branch: option tpp_sec_label) (prog: tpp_program) {measure (length (snd prog))} : option tpp_sec_label :=
    let '(nxt, instrs) := prog in 
    match instrs with 
    | nil             => tpp_check_instr env nxt
    | nxt' :: instrs' => 
      match branch with 
      | Some l => 
        let* r := tpp_check_instr env nxt in 
        if tsed l r
        then tpp_check_prog env branch (nxt', instrs')
        else None
      | None => 
        match nxt with 
        | TPPcondstore _ _ _
        | TPPcexec _ _ => 
          let* branch' := tpp_check_instr env nxt in 
          tpp_check_prog env (Some branch') (nxt', instrs')
        | _ => tpp_check_prog env branch (nxt', instrs')
        end
      end
    end.
    Solve All Obligations with (split; vm_compute; intros; congruence).

  Inductive instr_state := init.

  Record tpp_instr_store := mkInstrStore {
    prog : option tpp_program;
  }.

  Instance eta_tis : Settable _ := settable! mkInstrStore <prog >.

  Definition prog_len (p: tpp_program) := 1 + length (snd p).

  Program Definition tpp_instr_twopass_parser 
    (decoder : bytes 4 -> option tpp_instr)
    (policy: operand -> tpp_sec_label)
    (amount: nat)
    : p4automaton := {|
      size := fun _ => 4 * 8;
      update := fun _ bs (st : tpp_instr_store) => 
        let opcode := bits_8_to_byte (slice 0 8 bs) _ in 
        let o1 := bits_8_to_byte (slice 8 16 bs) _ in 
        let o2 := bits_8_to_byte (slice 16 24 bs) _ in 
        let o3 := bits_8_to_byte (slice 24 32 bs) _ in 
        let instr := decoder (opcode, (o1, (o2, (o3, tt)))) in 
        match instr, st.(prog) with 
        | None, _ => st <| prog := None |>
        | Some i, None => st <| prog := Some (i, nil) |>
        | Some i, Some prog' => 
          let '(oldi, oldis) := prog' in 
          st <| prog := Some (i, snoc oldi oldis) |>
        end;
      transitions := fun _ st =>
        match st.(prog) with 
        | Some prog' => 
          if prog_len prog' == amount then
            if tpp_check_prog policy None prog' 
            then inr true
            else inr false
          else inl init
        | None => inr false
        end;
    |}.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    lia.
    Qed.

    Record tpp_combined_store := mkCombinedStore {
      combined_prog : option tpp_program;
      constraint : option tpp_sec_label;
    }.

    Instance eta_tcs : Settable _ := settable! mkCombinedStore <combined_prog; constraint >.

  Program Definition tpp_instr_combined_parser 
    (decoder : bytes 4 -> option tpp_instr)
    (policy: operand -> tpp_sec_label)
    (amount: nat)
    : p4automaton := {|
      size := fun _ => 4 * 8;
      update := fun _ bs (st : tpp_combined_store) => 
        let opcode := bits_8_to_byte (slice 0 8 bs) _ in 
        let o1 := bits_8_to_byte (slice 8 16 bs) _ in 
        let o2 := bits_8_to_byte (slice 16 24 bs) _ in 
        let o3 := bits_8_to_byte (slice 24 32 bs) _ in 
        let instr := decoder (opcode, (o1, (o2, (o3, tt)))) in 
        match instr with 
        | None => st <| combined_prog := None |>
        | Some i => 
          match st.(combined_prog), tpp_check_instr policy i with 
          | _, None => st <| combined_prog := None |>
          | None, Some l =>
            match i with 
            | TPPcexec _ _
            | TPPcondstore _ _ _ =>
              st <| constraint := Some l |> <| combined_prog := Some (i, nil) |>
            | _ => st <| combined_prog := Some (i, nil) |>
            end
          | Some prog', Some l =>
            match st.(constraint) with 
            | Some l' => 
              if tsed l' l 
              then 
                let '(oldi, oldis) := prog' in 
                match i with 
                | TPPcexec _ _
                | TPPcondstore _ _ _ =>
                  st <| constraint := Some l |> <| combined_prog := Some (i, snoc oldi oldis) |>
                | _ => st <| combined_prog := Some (i, snoc oldi oldis) |>
                end
              else st <| combined_prog := None |>
            | None => st <| combined_prog := None |>
            end
          end
        end;
      transitions := fun _ st =>
        match st.(combined_prog) with 
        | Some prog' => 
          if prog_len prog' == amount 
          then inr true
          else inl init
        | None => inr false
        end;
    |}.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    eapply slice_n_n'.
    Qed.
    Next Obligation.
    split; vm_compute; intros; congruence.
    Qed.
    Next Obligation.
    split; vm_compute; intros; congruence.
    Qed.
    Next Obligation.
    split; vm_compute; intros; congruence.
    Qed.
    Next Obligation.
    split; vm_compute; intros; congruence.
    Qed.
    Next Obligation.
    lia.
    Qed.

  Require Import Poulet4.Examples.P4AutomatonValues.

    
  Inductive combined_twopass
    (decoder : bytes 4 -> option tpp_instr)
    (policy: operand -> tpp_sec_label) 
    (amount: nat)
    : 
    configuration (tpp_instr_twopass_parser decoder policy amount) ->
    configuration (tpp_instr_combined_parser decoder policy amount) ->
    Prop :=
    | Start :
      build_bisimulation
        (a1 := tpp_instr_twopass_parser decoder policy amount)
        (a2 := tpp_instr_combined_parser decoder policy amount)
        (fun s => 
          s.(prog) = None
        )
        (fun s => 
          s.(combined_prog) = None /\
          s.(constraint) = None
        )
        (inl init)
        (inl init)
        (fun buf buf' => buf = nil /\ buf = buf')
        (combined_twopass _ _ _)
      | TypeSuccess :
        forall prog',
        build_bisimulation
          (a1 := tpp_instr_twopass_parser decoder policy amount)
          (a2 := tpp_instr_combined_parser decoder policy amount)
          (fun s => 
            s.(prog) = Some prog'
          )
          (fun s => 
            s.(combined_prog) = Some prog'
          )
          (inl init)
          (inl init)
          (fun buf buf' => buf = nil /\ buf = buf')
          (combined_twopass _ _ _)
        | TypeFail :
          forall prog',
          build_bisimulation
            (a1 := tpp_instr_twopass_parser decoder policy amount)
            (a2 := tpp_instr_combined_parser decoder policy amount)
            (fun s => 
              s.(prog) = Some prog'
            )
            (fun s => 
              s.(combined_prog) = None
            )
            (inl init)
            (inr false)
            (fun buf buf' => True)
            (combined_twopass _ _ _)
      | End :
        forall b,
        build_bisimulation
          (a1 := tpp_instr_twopass_parser decoder policy amount)
          (a2 := tpp_instr_combined_parser decoder policy amount)
          store_top
          store_top
          (inr b)
          (inr b)
          (fun buf buf' => buf = buf')
          (combined_twopass _ _ _).

  
  Lemma combined_twopass_bis : 
    forall decoder policy amount, 
      bisimulation_with_leaps (combined_twopass decoder policy amount).
  Proof.
    unfold bisimulation_with_leaps.
    intros.
    inversion H;
    split; (split; intros; auto || exfalso; inversion H5) || intros; simpl in *.
    - destruct H2.
      rewrite H6 in *.
      rewrite H2 in *.
      simpl in *.
      destruct H1.
      unfold follow.
      unfold fold_left, step.
      destruct buf; [exfalso; inversion H5|].
      
      do 31 (destruct buf; [exfalso; simpl in H5; inversion H5|]).
      destruct buf; [|exfalso; simpl in H5; inversion H5].
      simpl length.
      simpl P4automaton.size'.
      do 31 (destruct (equiv_dec _ _); [inversion e|clear c]).
      simpl length.
      simpl P4automaton.size'.
      destruct (equiv_dec _ _); [clear e | exfalso; eapply c; auto].
      simpl "++".
      clear H5.

      set (bs' := [b; b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12;
      b13; b14; b15; b16; b17; b18; b19; b20; b21; b22; b23; b24;
      b25; b26; b27; b28; b29; b30]).

      simpl (update (_ _ _ _)).
      simpl (_ init [b; _]).
      simpl (transitions (_ _ _ _)).
      cbn delta.
      simpl ((fun _ => _) init) at 2.
      simpl ((fun _ => _) _) at 2.
      simpl ((fun _ => _) init) at 1.
      simpl ((fun _ => _) init).
      simpl ((fun _ => _) _) at 3.
      simpl ((fun _ => _) _) at 5.
      simpl ((fun _ => _) _) at 6.

      set (bs'0 := TPPautomaton.slice 0 8 bs').
      set (bs'1 := TPPautomaton.slice 8 16 bs').
      set (bs'2 := TPPautomaton.slice 16 24 bs').
      set (bs'3 := TPPautomaton.slice 24 32 bs').


      rewrite (bits_8_pf_irrel bs'0 (tpp_instr_twopass_parser_obligation_1 bs') (tpp_instr_combined_parser_obligation_1 bs')).
      rewrite (bits_8_pf_irrel bs'1 (tpp_instr_twopass_parser_obligation_2 bs') (tpp_instr_combined_parser_obligation_2 bs')).
      rewrite (bits_8_pf_irrel bs'2 (tpp_instr_twopass_parser_obligation_3 bs') (tpp_instr_combined_parser_obligation_3 bs')).
      rewrite (bits_8_pf_irrel bs'3 (tpp_instr_twopass_parser_obligation_4 bs') (tpp_instr_combined_parser_obligation_4 bs')).

      destruct (decoder _).
      * rewrite H0.
        unfold set.
        simpl prog.
        rewrite H1.
        simpl (prog _).
        cbn - [equiv_dec].

        destruct (tpp_check_instr policy t).

        + destruct t;
          simpl;
          destruct (equiv_dec _ _);
            now (eapply End; compute; auto) || 
            now (eapply TypeSuccess; compute; trivial; split; trivial).
        + destruct (equiv_dec _ _);
            now (eapply End; compute; auto) || 
            now (compute; eapply TypeFail; simpl; trivial).
      * compute.
        eapply End; compute; auto.
    -   destruct H2.
        subst buf1.
        subst buf2.
        simpl in H5.

        unfold follow.
        unfold fold_left, step.
        destruct buf; [exfalso; inversion H5|].
        
        do 31 (destruct buf; [exfalso; simpl in H5; inversion H5|]).
        destruct buf; [|exfalso; simpl in H5; inversion H5].

        simpl length.
        simpl P4automaton.size'.
        do 31 (destruct (equiv_dec _ _); [inversion e|clear c]).
        simpl length.
        simpl P4automaton.size'.
        destruct (equiv_dec _ _); [clear e | exfalso; eapply c; auto].
        simpl "++".
        clear H5.

        set (bs' := [b; b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12;
          b13; b14; b15; b16; b17; b18; b19; b20; b21; b22; b23; b24;
          b25; b26; b27; b28; b29; b30]).
        simpl (update (_ _ _ _)).
        simpl (_ init bs').
        simpl (transitions (_ _ _ _)).
        cbn delta.

        set (bs'0 := TPPautomaton.slice 0 8 bs').
        set (bs'1 := TPPautomaton.slice 8 16 bs').
        set (bs'2 := TPPautomaton.slice 16 24 bs').
        set (bs'3 := TPPautomaton.slice 24 32 bs').


        rewrite (bits_8_pf_irrel bs'0 (tpp_instr_twopass_parser_obligation_1 bs') (tpp_instr_combined_parser_obligation_1 bs')).
        rewrite (bits_8_pf_irrel bs'1 (tpp_instr_twopass_parser_obligation_2 bs') (tpp_instr_combined_parser_obligation_2 bs')).
        rewrite (bits_8_pf_irrel bs'2 (tpp_instr_twopass_parser_obligation_3 bs') (tpp_instr_combined_parser_obligation_3 bs')).
        rewrite (bits_8_pf_irrel bs'3 (tpp_instr_twopass_parser_obligation_4 bs') (tpp_instr_combined_parser_obligation_4 bs')).

        destruct (decoder _).
        * rewrite H0.
          destruct prog'.
          simpl.


          admit.

        * admit.



    - admit.
    - destruct buf; [exfalso; simpl in *; congruence|].
      destruct buf; [|exfalso; simpl in *; congruence].
      clear H5.
      simpl.
      subst buf1.
      destruct (equiv_dec _ _);
      eapply End; compute; auto.
  Admitted.
    

End TPP.