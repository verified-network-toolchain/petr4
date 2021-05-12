Require Import Paco.paco.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.AList.
Require Import Poulet4.Bitwise.
Require Import Poulet4.P4automata.P4automaton.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition to_val (w: nat) (bs: list bool) : @ValueBase Info :=
  let v := to_nat bs in
  ValBaseBit w (Z.of_nat v).

Definition mkField (s: string) : P4String.t Info :=
  {| P4String.tags := NoInfo ; str := s |}.

Definition mkEntry (s: string) (v: @ValueBase Info): P4String.t Info * ValueBase :=
  (mkField s, v).

Definition slice {A} to from (l: list A) := firstn (from - to) (skipn to l).

Instance StrEqDec : EqDec string eq := {
  equiv_dec := string_dec;
}.


(* Infinite trees, following the development in paco's tutorial.v. *)
CoInductive inftree :=
  | node : inftree -> inftree -> inftree.

Definition tunf t : inftree :=
  match t with node tl tr => node tl tr end.

Lemma tunf_eq : forall t, t = tunf t.
Proof.
  destruct t; auto.
Qed.

Inductive teq_gen teq : inftree -> inftree -> Prop :=
  | _teq_gen : forall t1l t1r t2l t2r (Rl : teq t1l t2l : Prop) (Rr : teq t1r t2r),
                 teq_gen teq (node t1l t1r) (node t2l t2r).
Hint Constructors teq_gen : core.

Definition teq t1 t2 : Prop := paco2 teq_gen bot2 t1 t2.
Hint Unfold teq : core.
Lemma teq_gen_mon: monotone2 teq_gen.
Proof.
 pmonauto.
Qed.
Hint Resolve teq_gen_mon : paco.

CoFixpoint i := node a b
with a := node e e
with b := node e e
with e := node i i.

CoFixpoint ii := node aa bb
with aa := node ee ee
with bb := node ee ee
with ee := node ii ii.

Theorem teq_i_ii:
  teq i ii.
Proof.
  ginit.
  Unshelve.
  3:exact (fun x => x).
  - constructor; auto.
    intros.
    inversion PR; subst.
    constructor; constructor; apply rclo2_base; tauto.
  - gcofix CIH.
    rewrite (tunf_eq i).
    rewrite (tunf_eq ii).
    gstep.
    simpl.
    constructor.
    + gcofix CIHa.
      rewrite (tunf_eq a).
      rewrite (tunf_eq aa).
      gstep.
      simpl.
      constructor;
        gcofix CIHe;
        rewrite (tunf_eq e);
        rewrite (tunf_eq ee);
        gstep;
        simpl;
        constructor; gbase; eauto.
    + gcofix CIHb.
      rewrite (tunf_eq b).
      rewrite (tunf_eq bb).
      gstep.
      simpl.
      constructor;
        gcofix CIHe;
        rewrite (tunf_eq e);
        rewrite (tunf_eq ee);
        gstep;
        simpl;
        constructor; gbase; eauto.
Qed.

Theorem teq_i_ii_better:
  teq i ii.
Proof.
  ginit.
  Unshelve.
  3:exact id.
  {
    unfold id.
    constructor; auto.
    intros.
    inversion PR; subst.
    constructor; constructor; apply rclo2_base; tauto.
  }
  gcofix CIH.
  rewrite (tunf_eq i).
  rewrite (tunf_eq ii).
  gstep.
  simpl.
  rewrite (tunf_eq a), (tunf_eq aa), (tunf_eq b), (tunf_eq bb).
  simpl.
  cut (gpaco2 teq_gen id r r (node e e) (node ee ee)).
  { eauto. }
  rewrite (tunf_eq e), (tunf_eq ee).
  simpl.
  gstep.
  cut (gpaco2 teq_gen id r r (node i i) (node ii ii)).
  { eauto. }
  gstep.
  constructor; gbase; auto.
Qed.

Theorem teq_i_ii_better_without_gpaco:
  teq i ii.
Proof.
  pcofix CIH.
  rewrite (tunf_eq i).
  rewrite (tunf_eq ii).
  pfold.
  simpl.
  rewrite (tunf_eq a), (tunf_eq aa), (tunf_eq b), (tunf_eq bb).
  simpl.
  cut (upaco2 teq_gen r (node e e) (node ee ee)).
  { eauto. }
  rewrite (tunf_eq e), (tunf_eq ee).
  simpl.
  left.
  cut (upaco2 teq_gen r (node i i) (node ii ii)).
  { eauto. }
  left.
  pfold.
  constructor; right; auto.
Qed.


Module BabyIPv1.
  Inductive states :=
  | start
  | parse_udp
  | parse_tcp
  .

  Definition size' (s: states) : nat :=
    match s with
    | start => 20
    | parse_udp => 20
    | parse_tcp => 28
    end
  .
  Definition values := @ValueBase Info.

  Record store' := MkStore {
    store_ip_hdr: values;
    store_u_or_t_hdr: values + values;
  }.

  Instance etaStore : Settable _ := settable! MkStore <store_ip_hdr; store_u_or_t_hdr >.

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        mkEntry "src" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dst" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "proto" (to_val 4 (slice 16 20 bs)) :: nil in
      st <| store_ip_hdr := ValBaseHeader fields true |>
    | parse_udp =>
      let fields :=
        mkEntry "sport" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dport" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "flags" (to_val 4 (slice 16 20 bs)) :: nil in
      st <| store_u_or_t_hdr := inl (ValBaseHeader fields true) |>
    | parse_tcp =>
      let fields :=
        mkEntry "sport" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dport" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "flags" (to_val 4 (slice 16 20 bs)) ::
        mkEntry "seq" (to_val 8 (slice 20 28 bs)) :: nil in
      st <| store_u_or_t_hdr := inr (ValBaseHeader fields true) |>
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      match st.(store_ip_hdr) with
      | ValBaseHeader fields true =>
        match AList.get fields (mkField "proto") with
        | Some (ValBaseBit 4 1) => inl parse_udp
        | Some (ValBaseBit 4 0) => inl parse_tcp
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_udp => inr true
    | parse_tcp => inr true
    end
  .

  Program Definition v1_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

  Record SwitchState := mkSwitchState {
    egress_spec : @ValueBase Info;
  }.

  Instance etaSwitchState : Settable _ := settable! mkSwitchState <egress_spec >.

  Definition v1_control (s: store') (state: SwitchState) : SwitchState :=
    match s.(store_u_or_t_hdr) with
    | inl (ValBaseHeader _ true) => state <| egress_spec := ValBaseBit 8 0 |>
    | _ => state <| egress_spec := ValBaseBit 8 1 |>
    end.

  Definition init_config: configuration v1_parser :=
    let blank_store := {| store_ip_hdr := ValBaseHeader nil false; store_u_or_t_hdr := inl (ValBaseHeader nil false) |} in
    (inl start, blank_store, nil).

  Definition v1_program (pkt: list bool) (state: SwitchState) : SwitchState :=
    let '(_, final_store, _) := follow init_config pkt in
    v1_control final_store state.

  Definition repr_tcp (bs: list bool) : Prop :=
    List.length bs = 48 /\ (to_nat (slice 16 20 bs) = 1).

  Lemma baby_ip_corr :
    forall pkt st st',
      repr_tcp pkt ->
      st' = v1_program pkt st ->
        accepted init_config pkt /\
        st'.(egress_spec) = ValBaseBit 8 0.
  Proof.
    intros.

    unfold repr_tcp in H.
    destruct H.
    rewrite H0.
    unfold v1_program.
    unfold egress_spec, accepted.
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    unfold slice in *.
    simpl in H1 |- *.
    rewrite H1.
    simpl.
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    do 10 (destruct pkt; [exfalso; inversion H| simpl]).
    unfold slice.
    simpl.
    do 8 (destruct pkt; [exfalso; inversion H| simpl]).
    destruct pkt.

    - simpl; split; unfold accepting; trivial.
    - exfalso. inversion H.

  Qed.
End BabyIPv1.

Module BabyIPv2.
  Inductive states :=
  | start
  | parse_tcp
  .

  Definition size' (s: states) : nat :=
    match s with
    | start => 40
    | parse_tcp => 8
    end
  .

  Definition values := @ValueBase Info.


  Record store' := MkStore {
    store_combined_hdr: values;
    store_optional_hdr: values;
  }.

  Instance etaStore : Settable _ := settable! MkStore <store_combined_hdr; store_optional_hdr>.

  Definition update' (s: states) (bs: list bool) (st: store') :=
    match s with
    | start =>
      let fields :=
        mkEntry "src" (to_val 8 (slice 0 8 bs)) ::
        mkEntry "dst" (to_val 8 (slice 8 16 bs)) ::
        mkEntry "proto" (to_val 4 (slice 16 20 bs)) ::
        mkEntry "sport" (to_val 8 (slice 20 28 bs)) ::
        mkEntry "dport" (to_val 8 (slice 28 36 bs)) ::
        mkEntry "flags" (to_val 4 (slice 36 40 bs)) :: nil in
        st <| store_combined_hdr := ValBaseHeader fields true |>
    | parse_tcp =>
      let fields :=
        mkEntry "seq" (to_val 8 (slice 0 8 bs)) :: nil in
        st <| store_optional_hdr := ValBaseHeader fields true |>
    end
  .

  Definition transitions' (s: states) (st: store') : states + bool :=
    match s with
    | start =>
      match st.(store_combined_hdr) with
      | ValBaseHeader fields true =>
        match AList.get fields (mkField "proto") with
        | Some (ValBaseBit 4 1) => inr true
        | Some (ValBaseBit 4 0) => inl parse_tcp
        | _ => inr false
        end
      | _ => inr false
      end
    | parse_tcp => inr true
    end
  .

  Program Definition v2_parser : p4automaton := {|
    size := size';
    update := update';
    transitions := transitions';
  |}.
  Next Obligation.
    destruct s; simpl; lia.
  Qed.

End BabyIPv2.

CoInductive tree V :=
| tleaf (val: V)
| tbranch (val: V) (l: tree V) (r: tree V).
Arguments tleaf {_}.
Arguments tbranch {_}.

CoFixpoint behavior (a: p4automaton) (c: configuration a) : tree (configuration a) :=
  match c with
  | (inl state, store, buf) =>
    tbranch c (behavior a (step c true))
              (behavior a (step c false))
  | (inr _, _, _) =>
    tleaf c
  end.

Inductive bisim_gen (a: p4automaton) (b: p4automaton) bisim : configuration a -> configuration b -> Prop :=
| bisim_gen_: forall c1 c2,
    (accepting c1 <-> accepting c2) ->
    bisim (step c1 true) (step c2 true) ->
    bisim (step c1 false) (step c2 false) ->
    bisim_gen a b bisim c1 c2.
Hint Constructors bisim_gen : core.

Definition bisim a b (c1: configuration a) (c2: configuration b) : Prop :=
  paco2 (bisim_gen a b) bot2 c1 c2.
Hint Unfold bisim : core.
Lemma bisim_gen_mon: forall a b, monotone2 (bisim_gen a b).
Proof.
  pmonauto.
Qed.
Hint Resolve bisim_gen_mon : paco.

Fixpoint steps {a} (c: configuration a) (bits: list bool) :=
  match bits with
  | nil => c
  | b::bits' => steps (step c b) bits'
  end.

Definition config_valid {a} (c: configuration a) :=
  match c with
  | (inl state, store, buf) =>
    List.length buf < size a state
  | _ =>
    True
  end.

Definition buffers {a} (c1 c2: configuration a) (bs: list bool) :=
  match c1, c2 with
  | (inl state1, store1, buf1),
    (inl state2, store2, buf2) =>
    List.length (buf1 ++ bs) < size a state1 /\
    steps c1 bs = c2
  | _, _ => c1 = c2
  end.

Ltac destruct_config c :=
  destruct c as [[[?|?] ?] ?].

Lemma buffers_refl {a}:
  forall (c: configuration a),
    config_valid c ->
    buffers c c nil.
Proof.
  intros.
  destruct_config c; simpl; auto.
  simpl in H.
  split.
  - rewrite app_length.
    simpl.
    lia.
  - reflexivity.
Qed.
Hint Resolve buffers_refl : paco.

Lemma buffers_nil {a}:
  forall (c c': configuration a),
    buffers c c' nil ->
    c = c'.
Proof.
  intros.
  destruct_config c;
    destruct_config c';
    simpl in H;
    try rewrite app_length in *;
    simpl in *;
    intuition congruence.
Qed.

Inductive buf_clo {a b} (R: configuration a -> configuration b -> Prop)
  : configuration a -> configuration b -> Prop :=
| buf_clo_: forall bs x0 y0 x y,
    buffers x x0 bs ->
    buffers y y0 bs ->
    (accepting x <-> accepting y) ->
    config_valid x ->
    config_valid y ->
    R x0 y0 ->
    buf_clo R x y.
Hint Constructors buf_clo : paco.

Lemma buf_clo_mono:
  forall a b, monotone2 (@buf_clo a b).
Proof.
  pmonauto.
Qed.
Hint Resolve buf_clo_mono : paco.

Lemma bisim_gen_id_compat:
  forall a b, wcompatible2 (bisim_gen a b) id.
Proof.
  unfold id.
  constructor; auto.
  intros.
  inversion PR; subst.
  constructor; eauto with paco.
Qed.
Hint Resolve bisim_gen_id_compat : paco.

Lemma bisim_gen_buf_clo_compat:
  forall a b, wcompatible2 (bisim_gen a b) buf_clo.
Proof.
Admitted.
Hint Resolve bisim_gen_buf_clo_compat : paco.

Lemma bisim_babyipv1_babyipv2 :
  forall st1 st2,
    bisim BabyIPv1.v1_parser
          BabyIPv2.v2_parser
          (inl BabyIPv1.start, st1, nil)
          (inl BabyIPv2.start, st2, nil).
Proof.
  intros.
  ginit.
  gcofix CIH.
  gclo.
  match goal with
  | |- ?G =>
    cut (forall (bs: list bool), List.length bs = 19 -> G)
  end.
  {
    intros.
    specialize (H (List.repeat true 19)).
    simpl in *; eauto.
  }
  intros.
  set (st1' := (@inl (states BabyIPv1.v1_parser) bool BabyIPv1.start, st1, bs)).
  set (st2' := (@inl (states BabyIPv2.v2_parser) bool BabyIPv2.start, st2, bs)).
  eapply (buf_clo_ _ bs st1' st2').
  - simpl.
    split; try lia.
    do 20 (destruct bs; try now inversion H).
  - simpl.
    split; try lia.
    do 20 (destruct bs; try now inversion H).
  - cbv. intuition congruence.
  - simpl. lia.
  - simpl. lia.
  - gstep.
    constructor.
    + cbv. intuition congruence.
    + gcofix CIH'.
      repeat (simpl || rewrite app_length || rewrite H).
      remember (slice 16 20 (bs ++ true :: nil)) as ip_type.
      destruct (match Z.of_nat (to_nat ip_type) with
                | 0%Z => inl BabyIPv1.parse_tcp
                | 1%Z => inl BabyIPv1.parse_udp
                | _ => inr false
                end)
               eqn:?.
      destruct s.
      * admit.
      * assert (ip_type = false::false::false::nil).
        { admit. }
        gstep.
        (* stuck *)
        admit.
      * admit.
      * admit.
    + admit.
Abort.
