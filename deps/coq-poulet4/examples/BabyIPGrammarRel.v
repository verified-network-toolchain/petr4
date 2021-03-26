Require Import Syntax.
Require Import BabyIP.
Require Import SimpleIPv4.
Require Import P4defs.
Require Import Step.
Require Import P4String.

Require Import Environment.Environment.
Require Import Petr4.Monads.Monad.
Require Import Petr4.Monads.P4Monad.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.
Import AList.

Open Scope nat_scope.
Open Scope monad_scope.

Definition MkP4String s := {| tags := NoInfo; str := s |}.

Definition empty_env :=
    {| env_fresh := 0;
       env_stack := MStr.empty loc :: nil;
       env_heap := MNat.empty (@Value P4defs.Info); |}.

Definition init_parser_state pkt :=
  let packet := ValObj (ValObjPacket pkt) in
  env_insert P4defs.Info "packet" packet ;;
  env_insert P4defs.Info "hdr" (ValBase (ValBaseHeader ((MkP4String "ip", ValBaseHeader ((MkP4String "src", ValBaseBit 8 0) :: (MkP4String "dst", ValBaseBit 8 0) :: (MkP4String "proto", ValBaseBit 4 0) :: nil) false) :: (MkP4String "t_or_u", ValBaseUnion ((MkP4String "udp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: nil) false) :: (MkP4String "tcp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: (MkP4String "seq", ValBaseBit 8 0) :: nil) false) :: nil)) :: nil) false)).

Definition make_stepper params constructor_params locals states :=
    let scope := MkEnv_EvalEnv nil nil (MkP4String "dummy") in
    let parser := ValObjParser scope params constructor_params locals states in
    step_trans _ NoInfo parser 2 (MkP4String "start").

Definition make_parser pkt parser :=
  match parser with
  | DeclParser _ _ _ params constructor_params locals states =>
    init_parser_state pkt ;; make_stepper params constructor_params locals states
  | _ => State.state_fail Internal
  end.

Definition eval_parser pkt parser : option (Value * list bool) :=
  match make_parser pkt parser empty_env with
  | (inl _, env) =>
    let get_pkt_and_hdr :=
        let* pkt_val := env_str_lookup P4defs.Info (MkP4String "packet") in
        let* hdr_val := env_str_lookup P4defs.Info (MkP4String "hdr") in
        mret (hdr_val, pkt_val)
    in
    match get_pkt_and_hdr env  with
    | (inl (hdr, (ValObj (ValObjPacket pkt))), env) => Some (hdr, pkt)
    | _ => None
    end
  | (inr _, _) => None
  end.

Definition bits_repr (n: nat) (bs: bits n) (v: @ValueBase P4defs.Info) : Prop :=
  match v with
  | ValBaseBit n' z => n = n' /\ Some z = bits2Z bs
  | _ => False
  end.

Inductive val_repr: forall (t: Type), t -> @ValueBase P4defs.Info -> Prop :=
| VRBits: forall n u v,
    bits_repr n u v ->
    val_repr (bits n) u v.

(* I wrote this by using tactics and then hand-simplifying the
   resulting term. - Ryan *)
Definition header_repr (fields: AList.AList string Type eq) (rec: HAList.t fields)
  : list (P4String.t P4defs.Info * @ValueBase P4defs.Info) -> Prop :=
  HAList.t_rect
    (fun fields (t1 : HAList.t fields) => forall rec0, rec0 = t1 -> list (t Info * ValueBase) -> Prop)
    (fun _ _ v =>
       v = [])
    (fun (k: string) (typ: Type) _ (rec_val: typ) rec' header_repr _ _ v =>
       match v with
       | [] => False
       | (field_name, field_val) :: v' =>
         field_name.(str) = k /\
         val_repr typ rec_val field_val /\
         header_repr rec' eq_refl v'
       end)
    fields rec rec eq_refl.
Arguments header_repr {_%list_scope} _ _%list_scope.

Definition value_repr {fields} (rec: HAList.t fields) (val: @Value P4defs.Info): Prop :=
  match val with
  | ValBase (ValBaseHeader hdr true) => header_repr rec hdr
  | _ => False
  end.

Notation P4String := (P4String.t Info).

Definition bits_equiv_header (val: P4String.AList P4defs.Info (@ValueBase P4defs.Info)) (key: string) (n: nat) (other: option (bits n)) :=
  match AList.get val (MkP4String key), other with
  | Some (ValBaseBit n' b), Some other' =>
    n = n' /\ bits2Z other' = Some b
  | _, _ => False
  end
.

Definition packet_repr (bits: list bool) (pkt: @Value P4defs.Info) : Prop :=
  pkt = ValObj (ValObjPacket bits).

Lemma init_parser_state_ok:
  forall pk res st,
    init_parser_state pk empty_env = (res, st) ->
    res = inl tt.
Proof.
  unfold init_parser_state.
  cbv.
  congruence.
Qed.

Theorem init_parser_state_sound:
  forall pk init_state_p4 init_state_monad,
    init_parser_state pk empty_env = (inl tt, init_state_p4) ->
    init_state pk = init_state_monad ->
    exists pk' env',
      env_str_lookup P4defs.Info (MkP4String "packet") init_state_p4 = (inl pk', env') /\
      packet_repr init_state_monad.(pkt) pk'.
Proof.
  intros.
  cbv in H.
  inversion H.
  do 2 eexists.
  cbv.
  split.
  - reflexivity.
  - rewrite <- H0.
    reflexivity.
Qed.

Scheme LVal_ind := Induction for ValueLvalue Sort Prop
  with PreLVal_ind := Induction for ValuePreLvalue Sort Prop.

Definition env_invariant
  {St Exception Result}
  (m: @State.state_monad St Exception Result)
:=
  forall env,
    snd (m env) = env
.

Lemma env_name_lookup_no_write:
  forall name,
    env_invariant (env_name_lookup P4defs.Info name)
.
Proof.
Admitted.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac name_bind H := 
  match type of H with
  | context [ State.state_bind ?f ?n ?i ] =>
    unfold State.state_bind in H;
    let F := fresh "f" in remember (f i) as F;
    let N := fresh "n" in remember n as N
  | context [ State.state_bind ?f ?n ] =>
    let F := fresh "f" in remember f as F;
    let N := fresh "n" in remember n as N
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

Lemma env_invariant_preserve
  {St Result Result' Exception: Type}:
  forall m (f: Result -> @State.state_monad St Exception Result'),
    env_invariant m ->
    (forall r, env_invariant (f r)) ->
    env_invariant (State.state_bind m f)
.
Proof.
  unfold env_invariant.
  intros.
  unfold State.state_bind.
  break_let.
  break_match.
  - rewrite H0.
    rewrite <- H.
    rewrite Heqp.
    reflexivity.
  - simpl.
    rewrite <- H.
    rewrite Heqp.
    reflexivity.
Qed.

Lemma env_invariant_lift_opt_some
  {St Exception Result: Type}:
  forall e f, @env_invariant St Exception Result (Transformers.lift_opt e f).
Proof.
  unfold env_invariant, Transformers.lift_opt; intros.
  break_match; reflexivity.
Qed.

Lemma env_lookup_no_write:
  forall lval,
    env_invariant (env_lookup P4defs.Info lval)
.
Proof.
  set (P0 := fun pre_lval =>
               forall t,
                 env_invariant (env_lookup P4defs.Info (MkValueLvalue pre_lval t))).
  induction lval using LVal_ind with (P0 := P0);
    unfold P0 in *; intros; simpl in *;
    eauto using env_invariant_preserve,
        env_name_lookup_no_write,
        env_invariant_lift_opt_some.
Qed.

Lemma stack_push_lookup_invariant:
    forall str env env' val,
        env_str_lookup _ str env = (inl val, env) ->
        stack_push _ env = (inl tt, env') ->
        env_str_lookup Info str env' = (inl val, env')
.
Proof.
  intros.
  unfold stack_push in H0.
  inversion H0.
  unfold env_str_lookup in *.
  unfold env_name_lookup in *.
  simpl in *.
  unfold State.state_bind in *.
  break_let.
  unfold stack_lookup in *.
  destruct (stack_lookup' _ _) eqn:?.
Admitted.

Lemma parser_start_state_sound:
  forall scope constructor_params params locals states env env' hdr hdr' p p' next_state parser_state,
    env_str_lookup _ (MkP4String "packet") env = (inl (ValObj (ValObjPacket p)), env) ->
    lookup_state _ states (MkP4String "start") = Some MyParser_start ->
    step _ NoInfo (ValObjParser scope constructor_params params locals states)
         (MkP4String "start") env
      = (inl next_state, env') ->
    env_str_lookup _ (MkP4String "header") env' = (inl hdr, env') ->
    env_str_lookup _ (MkP4String "packet") env' = (inl (ValObj (ValObjPacket p')), env') ->
    State.run_with_state (init_state p) IPHeader_p = (inl hdr', parser_state) ->
    (* value_repr hdr' hdr /\ *)
    p' = parser_state.(pkt)
.
Proof.
  intros.
  simpl step in H1.
  rewrite H0 in H1.
  simpl in H1.
  rewrite Eval.eval_statement_equation_1 in H1.
  rewrite Eval.eval_statement_pre_equation_5 in H1.
  simpl in H1.
  rewrite Eval.eval_block_equation_2 in H1.
  simpl in H1.
  rewrite Eval.eval_statement_equation_1 in H1.
  name_bind H1.
  name_bind Heqf.
  name_bind Heqn0.
  name_bind Heqf1.
  rewrite Eval.eval_statement_pre_equation_1 in Heqf2.
  unfold Eval.eval_method_call in Heqf2.
  simpl in Heqf2.
  name_bind Heqf2.
  rewrite Eval.eval_expression_equation_1 in Heqf3.
  unfold State.state_bind in H1.
Admitted.

Theorem parser_grammar_sound :
  forall p p' hdr hdr_rec parser_state,
    eval_parser p MyParser = Some (hdr, p') ->
    State.run_with_state (init_state p) Headers_p = (inl hdr_rec, parser_state) ->
    value_repr hdr_rec hdr /\
    p' = parser_state.(pkt).
Proof.
  unfold eval_parser, make_parser.
  intros.
  destruct MyParser eqn:?; try (unfold MyParser in *; congruence).
  simpl in H.
  unfold State.state_bind in H.
  destruct (init_parser_state p empty_env) eqn:?.
  pose proof (Hieq := Heqp0).
  apply init_parser_state_ok in Hieq; subst.
  eapply init_parser_state_sound in Heqp0; eauto.
  destruct Heqp0 as [pk' [env' [Hlookup Hrepr]]].
  unfold make_stepper in H.
Admitted.
