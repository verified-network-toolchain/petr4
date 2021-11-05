Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.Step.
Require Import Poulet4.P4String.

Require Import Poulet4.Examples.BabyIP.
Require Import Poulet4.Examples.SimpleIPv4.

Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.P4Monad.

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
Polymorphic Definition header_repr (fields: AList.AList string Type eq) (rec: HAList.t fields)
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

Polymorphic Definition value_repr {fields} (rec: HAList.t fields) (val: @Value P4defs.Info): Prop :=
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

Lemma split_bind:
  forall {St Exception Result Result': Type} f g o s s',
    @State.state_bind St Exception Result Result' f g s = (inl o, s') ->
    exists s'' m, f s = (inl m, s'') /\ g m s'' = (inl o, s')
.
Proof.
  intros.
  unfold State.state_bind in H.
  break_let.
  destruct s0; try discriminate.
  exists s1, r.
  easy.
Qed.

Ltac split_bind_tac H :=
  match type of H with
  | State.state_bind ?f ?n ?s = (inl ?v, ?s') =>
    apply split_bind in H;
    let Hs := fresh s in
    let Hm := fresh "v" in
    let Hn := fresh H in
    destruct H as [Hs [Hm [H Hn]]];
    match type of Hm with
    | unit => destruct Hm
    | _ => idtac
    end
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

Lemma stack_lookup'_push_invariant:
  forall var env env',
    stack_push _ env = (inl tt, env') ->
    stack_lookup' var (env_stack Info env) = stack_lookup' var (env_stack Info env').
Proof.
  unfold stack_push.
  intros.
  simpl in H.
  inversion H.
  subst.
  clear H.
  reflexivity.
Qed.

Lemma stack_lookup_no_effect:
  forall s env res e,
    stack_lookup Info s env = (res, e) ->
    env = e.
Proof.
  unfold stack_lookup.
  intros.
  break_match; inversion H; auto.
Qed.

Lemma stack_push_lookup_invariant:
    forall str env env' val,
        env_str_lookup _ str env = (inl val, env) ->
        stack_push _ env = (inl tt, env') ->
        env_str_lookup Info str env' = (inl val, env')
.
Proof.
  intros.
  unfold env_str_lookup in *.
  unfold env_name_lookup in *.
  simpl in *.
  split_bind_tac H.
  unfold State.state_bind.
  unfold stack_lookup in *.
  erewrite <- stack_lookup'_push_invariant.
  2: { exact H0. }
  destruct (stack_lookup' _ _); try discriminate.
  simpl.
  inversion H.
  unfold heap_lookup in *.
  replace (env_heap Info env') with (env_heap Info env0).
  break_match; try discriminate.
  inversion H1.
  reflexivity.
  unfold stack_push in H0.
  inversion_clear H0.
  simpl.
  congruence.
Qed.

Definition not_in_top_scope env str :=
  match env_stack Info env with
  | top :: _ =>
    MStr.find str top = None
  | _ => False
  end
.

Lemma stack_pop_lookup_invariant:
  forall name env env' loc,
    stack_lookup _ name env = (inl loc, env) ->
    not_in_top_scope env name ->
    stack_pop _ env = (inl tt, env') ->
    stack_lookup _ name env' = (inl loc, env')
.
Proof.
  intros.
  unfold not_in_top_scope in H0.
  destruct (env_stack _ env) eqn:?; try contradiction.
  unfold stack_lookup in *.
  rewrite Heqs in H.
  simpl in H.
  rewrite H0 in H.
  unfold stack_pop in H1.
  rewrite Heqs in H1.
  inversion_clear H1.
  simpl.
  break_match; try discriminate.
  unfold State.state_return in *.
  congruence.
Qed.

Lemma heap_pop_lookup_invariant:
  forall loc env env' val,
    heap_lookup Info loc env = (inl val, env) ->
    stack_pop Info env = (inl tt, env') ->
    heap_lookup Info loc env' = (inl val, env')
.
Proof.
  intros.
  destruct env.
  destruct env_stack; try discriminate.
  unfold stack_pop in H0.
  simpl in H0.
  unfold State.state_return in H0.
  inversion_clear H0.
  unfold heap_lookup in *.
  simpl in *.
  break_match; try discriminate.
  unfold State.state_return in *.
  congruence.
Qed.

Lemma stack_pop_env_lookup_invariant:
    forall name env env' val,
        env_str_lookup _ name env = (inl val, env) ->
        not_in_top_scope env (str name) ->
        stack_pop _ env = (inl tt, env') ->
        env_str_lookup Info name env' = (inl val, env')
.
Proof.
  intros.
  unfold env_str_lookup, env_name_lookup in *.
  simpl in *.
  split_bind_tac H.
  unfold State.state_bind.
  assert (env = env0).
  eapply stack_lookup_no_effect.
  exact H.
  erewrite stack_pop_lookup_invariant.
  - eapply heap_pop_lookup_invariant.
    + rewrite H3 in H2.
      exact H2.
    + rewrite <- H3.
      exact H1.
  - rewrite H3 in H.
    exact H.
  - rewrite <- H3.
    exact H0.
  - rewrite <- H3.
    exact H1.
Qed.

Inductive not_declared_in_block {tags: Type}: string -> @Block tags -> Prop :=
| NotDeclaredInBlockEmpty: forall name tag, not_declared_in_block name (BlockEmpty tag)
| NotDeclaredInBlockCons:
    forall name block stmt,
      not_declared_in_statement name stmt ->
      not_declared_in_block name block ->
      not_declared_in_block name (BlockCons stmt block)
with not_declared_in_statement_pre {tags: Type}: string -> @StatementPreT tags -> Prop :=
| NotDeclaredInStatMethodCall:
    forall name func type_args args,
      not_declared_in_statement_pre name (StatMethodCall func type_args args)
| NotDeclaredInStatAssignment:
    forall name lhs rhs,
      not_declared_in_statement_pre name (StatAssignment lhs rhs)
| NotDeclaredInStatDirectApplication:
    forall name typ args,
      not_declared_in_statement_pre name (StatDirectApplication typ args)
| NotDeclaredInStatConditional:
    forall name cond tru fls,
      not_declared_in_statement name tru ->
      not_declared_in_statement_maybe name fls ->
      not_declared_in_statement_pre name (StatConditional cond tru fls)
| NotDeclaredInStatBlock:
    forall name block,
      not_declared_in_block name block ->
      not_declared_in_statement_pre name (StatBlock block)
| NotDeclaredInStatExit:
    forall name,
      not_declared_in_statement_pre name StatExit
| NotDeclaredInStatEmpty:
    forall name,
      not_declared_in_statement_pre name StatEmpty
| NotDeclaredInStatReturn:
    forall name expr,
      not_declared_in_statement_pre name (StatReturn expr)
| NotDeclaredInStatVariable:
    forall name typ name' init,
      name <> name'.(str) ->
      not_declared_in_statement_pre name (StatVariable typ name' init)
| NotDeclaredInStatInstantiation:
    forall name typ args name' init,
      name <> name'.(str) ->
      not_declared_in_statement_pre name (StatInstantiation typ args name' init)
with not_declared_in_statement {tags: Type}: string -> @Statement tags -> Prop :=
| NotDeclaredInMkStatement:
    forall name stmt typ tag,
      not_declared_in_statement_pre name stmt ->
      not_declared_in_statement name (MkStatement tag stmt typ)
with not_declared_in_statement_maybe {tags: Type}: string -> option (@Statement tags) -> Prop :=
| NotDeclaredInStatementMaybeNone:
    forall name, 
      not_declared_in_statement_maybe name None
| NotDeclaredInStatementMaybeSome:
    forall name stmt,
      not_declared_in_statement name stmt ->
      not_declared_in_statement_maybe name (Some stmt)
.

Definition not_in_top_scope_invariant {T: Type} (f: env_monad Info T) name :=
  forall env env' val,
    not_in_top_scope env name ->
    f env = (inl val, env') ->
    not_in_top_scope env' name
.

Lemma not_in_top_scope_invariant_bind {Result Result'}:
  forall (f: env_monad Info Result) (g: Result -> env_monad Info Result') name,
    not_in_top_scope_invariant f name ->
    (forall env, not_in_top_scope_invariant (g env) name) ->
    not_in_top_scope_invariant (State.state_bind f g) name
.
Proof.
  intros.
  unfold not_in_top_scope_invariant in *.
  intros.
  split_bind_tac H2.
  eapply H0.
  - eapply H.
    + exact H1.
    + exact H2.
  - exact H3.
Qed.

Lemma not_in_top_scope_invariant_toss_value:
  forall f name,
    not_in_top_scope_invariant f name ->
    not_in_top_scope_invariant (toss_value _ f) name
.
Proof.
  unfold not_in_top_scope_invariant, toss_value.
  intros.
  break_let.
  break_match; try discriminate.
  eapply H.
  - exact H0.
  - simpl in H1.
    inversion H1.
    rewrite Heqp.
    f_equal.
    assumption.
Qed.

Lemma not_in_top_scope_invariant_eval_expression:
  forall expr name,
    not_in_top_scope_invariant (Eval.eval_expression Info NoInfo expr) name
.
Admitted.

Lemma not_in_top_scope_invariant_state_fail:
  forall err name res,
    not_in_top_scope_invariant (@State.state_fail _ _ res err) name
.
Proof.
  intros.
  unfold not_in_top_scope_invariant.
  intros.
  unfold State.state_fail in H0.
  inversion H0.
Qed.

Lemma not_in_top_scope_invariant_state_return:
  forall R res name,
    not_in_top_scope_invariant (@State.state_return _ _ R res) name
.
Proof.
  intros.
  unfold not_in_top_scope_invariant.
  intros.
  unfold State.state_return in H0.
  inversion H0.
  congruence.
Qed.

Lemma not_in_top_scope_invariant_heap_insert:
  forall val name,
    not_in_top_scope_invariant (heap_insert Info val) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_eval_lvalue:
  forall expr name,
    not_in_top_scope_invariant (Eval.eval_lvalue Info expr) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_env_lookup:
  forall lval name,
    not_in_top_scope_invariant (env_lookup Info lval) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_eval_builtin_func:
  forall name' caller type_args args name,
    not_in_top_scope_invariant (Eval.eval_builtin_func Info name' caller type_args args) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_eval_copy_out:
  forall args_and_lvals name,
    not_in_top_scope_invariant (Eval.eval_copy_out _ args_and_lvals) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_env_update:
  forall lval val name,
    not_in_top_scope_invariant (env_update Info lval val) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_env_insert:
  forall name name' val,
    name <> name' ->
    not_in_top_scope_invariant (env_insert Info name' val) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_stack_push:
  forall name,
    not_in_top_scope_invariant (stack_push Info) name
.
Proof.
Admitted.

Lemma not_in_top_scope_invariant_eval_copy_in:
  forall l args name,
    not_in_top_scope_invariant (Eval.eval_copy_in Info NoInfo (Eval.eval_expression Info NoInfo) l args) name
.
Proof.
  induction l, args; intros.
  - rewrite Eval.eval_copy_in_equation_1.
    apply not_in_top_scope_invariant_state_return.
  - rewrite Eval.eval_copy_in_equation_2.
    apply not_in_top_scope_invariant_state_fail.
  - rewrite Eval.eval_copy_in_equation_3.
    apply not_in_top_scope_invariant_state_fail.
  - destruct o.
    + rewrite Eval.eval_copy_in_equation_4.
      simpl.
      break_let.
      apply not_in_top_scope_invariant_bind; try break_match;
      eauto using not_in_top_scope_invariant_bind,
                  not_in_top_scope_invariant_state_fail,
                  not_in_top_scope_invariant_state_return,
                  not_in_top_scope_invariant_heap_insert,
                  not_in_top_scope_invariant_eval_expression,
                  not_in_top_scope_invariant_eval_lvalue,
                  not_in_top_scope_invariant_env_lookup.
     + rewrite Eval.eval_copy_in_equation_5.
       break_match.
       simpl.
       destruct opt.
       eauto using not_in_top_scope_invariant_bind,
                   not_in_top_scope_invariant_state_return.
       apply not_in_top_scope_invariant_state_fail.
Qed.

Lemma block_not_in_top_scope:
  forall block name,
    not_declared_in_block name block ->
    not_in_top_scope_invariant (Eval.eval_block Info NoInfo block) name
.
Proof.
  induction block using @block_rec with
    (PStatementSwitchCase := fun _ => True)
    (PStatementSwitchCaseList := fun _ => True)
    (PStatementPreT := fun stmt => forall name, not_declared_in_statement_pre name stmt -> not_in_top_scope_invariant (Eval.eval_statement_pre Info NoInfo stmt) name)
    (PStatement := fun stmt => forall name, not_declared_in_statement name stmt -> not_in_top_scope_invariant (Eval.eval_statement Info NoInfo stmt) name)
    (PStatementMaybe := fun stmt_maybe => forall name stmt, stmt_maybe = Some stmt -> not_declared_in_statement_maybe name stmt_maybe -> not_in_top_scope_invariant (Eval.eval_statement Info NoInfo stmt) name)
    (PBlockMaybe := fun block_maybe => True); intros; try easy.
  - rewrite Eval.eval_statement_pre_equation_1.
    apply not_in_top_scope_invariant_toss_value.
    unfold Eval.eval_method_call.
    simpl.
    apply not_in_top_scope_invariant_bind.
    + unfold Unpack.unpack_func.
      simpl.
      apply not_in_top_scope_invariant_bind.
      * apply not_in_top_scope_invariant_eval_expression.
      * intros.
        break_match; try break_match;
        eauto using not_in_top_scope_invariant_state_fail,
                    not_in_top_scope_invariant_state_return.
    + intros.
      break_let.
      break_match;
      eauto using not_in_top_scope_invariant_eval_copy_in,
                  not_in_top_scope_invariant_state_fail,
                  not_in_top_scope_invariant_eval_builtin_func,
                  not_in_top_scope_invariant_bind,
                  not_in_top_scope_invariant_state_return,
                  not_in_top_scope_invariant_eval_copy_out.
  - rewrite Eval.eval_statement_pre_equation_2.
    eauto using not_in_top_scope_invariant_bind,
                not_in_top_scope_invariant_eval_expression,
                not_in_top_scope_invariant_eval_lvalue,
                not_in_top_scope_invariant_env_update.
  - rewrite Eval.eval_statement_pre_equation_5.
    simpl.
    eauto using not_in_top_scope_invariant_bind,
                not_in_top_scope_invariant_stack_push.
    admit.
  - rewrite Eval.eval_statement_pre_equation_7.
    eauto using not_in_top_scope_invariant_state_return.
  - rewrite Eval.eval_statement_pre_equation_11.
    simpl.
    inversion H.
    break_match;
    eauto using not_in_top_scope_invariant_bind,
                not_in_top_scope_invariant_eval_expression,
                not_in_top_scope_invariant_state_return,
                not_in_top_scope_invariant_env_insert.
  - rewrite Eval.eval_statement_equation_1.
    apply IHblock.
    inversion H.
    assumption.
  - inversion H.
    rewrite <- H2.
    apply IHblock.
    inversion H0.
    assumption.
  - rewrite Eval.eval_block_equation_1.
    apply not_in_top_scope_invariant_state_return.
  - rewrite Eval.eval_block_equation_2.
    simpl.
    inversion H.
    eauto using not_in_top_scope_invariant_bind.
Admitted.

Lemma ipheader_packet_effect:
  forall p hdr' parser_state,
    State.run_with_state (init_state p) IPHeader_p = (inl hdr', parser_state) ->
    parser_state.(pkt) = skipn 20 p.
Proof.
  (* John try proving this *)
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
    value_repr hdr' hdr /\
    p' = parser_state.(pkt)
.
Proof.
  intros.
  simpl step in H1.
  rewrite H0 in H1.
  break_let.
  split_bind_tac H1.
  assert (env_str_lookup Info (MkP4String "packet") env0 =
          (inl (ValObj (ValObjPacket (pkt parser_state))), env0)).
  {
    rewrite Eval.eval_statement_equation_1 in H1.
    rewrite Eval.eval_statement_pre_equation_5 in H1.
    simpl in H1.
    split_bind_tac H1.
    split_bind_tac H6.
    apply stack_pop_env_lookup_invariant with (env := env2); try assumption.
    2: {
      simpl.
      injection Heqp0.
      intros Htransition Hstatements Hname Htags.
      assert (not_in_top_scope_invariant (Eval.eval_block Info NoInfo (states_to_block Info NoInfo statements)) "packet").
      apply block_not_in_top_scope.
      admit.
      unfold not_in_top_scope_invariant in H8.
      eapply H8.
      2: { exact H6. }
      admit.
    }
    admit.
  }
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
  unfold step_trans in H.
  simpl in H.
  inversion Heqd.
  rewrite <- H8 in H.
  unfold State.state_bind in H.
  unfold lookup_state in H.
  simpl in H.
Admitted.
  (*
  autorewrite with eval_statement in H.
  simpl in H.
  unfold State.state_bind, stack_push, toss_value in H.
  simpl in H.
  unfold Eval.eval_method_call in H.
  simpl in H.
  unfold State.state_bind, Unpack.unpack_func in H.
  autorewrite with eval_expression in H.
  simpl in H.
  unfold stack_lookup, heap_lookup, stack_lookup' in H.
  simpl in H.
  unfold State.state_bind, State.state_return in H.
  unfold env_stack in H.
  simpl in H.

  destruct e.

  fold stack_lookup' in H.
  assert (exists pkt, stack_lookup' "packet" env_stack = Some pkt).
  admit.
  destruct H1.
  rewrite H1 in H.
  assert (MNat.find (elt:=Value) x env_heap = Some pk').
  admit.
  simpl in H.
  rewrite H9 in H.
  assert (exists conc_pkt, pk' = ValObj (ValObjPacket conc_pkt)).
  admit.
  destruct H10.
  rewrite H10 in H.
  unfold Eval.extract_value_func in H.
  autorewrite with eval_copy_in eval_expression in H.
  simpl in H.
  unfold Eval.eval_builtin_func in H.
  unfold Eval.eval_is_valid in H. simpl in H.
  unfold Eval.eval_packet_func in H.
  simpl in H.
  unfold Transformers.lift_opt, Unpack.unpack_packet, env_name_lookup, State.state_bind in H.
  simpl in H.
  unfold State.state_bind in H.
  simpl in H.
  unfold stack_lookup in H.
  simpl in H.
  rewrite H1 in H.
  simpl in H.
  unfold heap_lookup in H.
  simpl in H.
  assert (MNat.find (elt:=Value) x
    (MNat.add env_fresh
      (Eval.default_value Info NoInfo
        TypVoid) env_heap) = MNat.find (elt:=Value) x
         env_heap).
  admit.
  rewrite H11 in H.
  rewrite H9 in H.
  simpl in H.
  rewrite H10 in H.
  simpl in H.
  unfold State.state_bind in H.
  do 8 (destruct x0; [exfalso; simpl in H; rewrite H1 in H; simpl in H; inversion H |]).
  simpl in H.
  do 8 (destruct x0; [exfalso; simpl in H; rewrite H1 in H; simpl in H; inversion H |]).
  simpl in H.
  do 4 (destruct x0; [exfalso; simpl in H; rewrite H1 in H; simpl in H; inversion H |]).
  simpl in H.
  rewrite H1 in H.
  simpl in H.
  autorewrite with eval_copy_out in H.
  simpl in H.
  unfold heap_lookup, State.state_bind, env_name_lookup, Transformers.lift_opt in H. simpl in H.
  simpl in H.
  assert (forall T k (v: @Value T) e, MNat.find (elt:=@Value T) k (MNat.add k v e) = Some v).
  admit.
  specialize (H12 Info env_fresh).
  erewrite H12 in H. simpl in H.
  unfold stack_lookup, heap_lookup, State.state_bind in H. simpl in H.
  assert (exists x_hdr, stack_lookup' "hdr" env_stack = Some x_hdr).
  admit.
  destruct H13.
  rewrite H13 in H.
  simpl in H.
  assert (forall T k k' (pf: k <> k') (v: @Value T) e, MNat.find (elt:=@Value T) k (MNat.add k' v e) = MNat.find (elt := @Value T) k e).
  admit.

  assert (x1 <> env_fresh).
  admit.
  erewrite (H14 Info x1 env_fresh H15) in H.
  assert (x1 <> x).
  admit.
  erewrite (H14 Info x1 x H16) in H.
  erewrite (H14 Info x1 env_fresh H15) in H.
  assert (exists hdr_val, MNat.find (elt:=Value) x1 env_heap = Some hdr_val).
  admit.
  destruct H17.
  rewrite H17 in H. simpl in H.
  
  do 8 (destruct x0; [exfalso; simpl in H; rewrite H1 in H; simpl in H; inversion H |]).
  simpl in H.

  
  unfold MNat.find in H.
  fold MNat.find in H.
  rewrite H9 in H.
  assert (stack_lookup Info "packet"
  {|
    env_fresh := S env_fresh;
    env_stack :=
      MStr.empty loc :: env_stack;
    env_heap :=
      MNat.add env_fresh
        (Eval.default_value Info NoInfo
           TypVoid) env_heap
  |} = stack_lookup' "packet" env_stack).

  rewrite H1 in H.
  unfold Eval.eval_copy_in in H.
  rewrite H11 in H.
  unfold Eval.eval_statement in H.
  cbv in H.
  simpl in H.
Admitted. *)
