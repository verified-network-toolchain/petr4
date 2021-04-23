Require Import Poulet4.Examples.BabyIP.
Require Import Poulet4.P4defs.
Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Eval.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Monads.Hoare.WP.

Open Scope string_scope.

Import ListNotations.

Lemma case_val_wp_p 
  {tags_t: Type}
  {State Exception Result: Type} 
  {P1 P2 P3 Q c1 c2} 
  {c3: ValueConstructor -> @state_monad State Exception Result}
  v:
  (forall vb, v = @ValBase tags_t vb -> << fun s => P1 vb s >> c1 vb << Q >>) ->
  (forall vo, v = @ValObj tags_t vo -> << fun s => P2 vo s >> c2 vo << Q >>) ->
  (forall vc, v = @ValCons tags_t vc -> << fun s => P3 vc s >> c3 vc << Q >>) ->
  << 
    match v with 
    | ValBase vb => P1 vb
    | ValObj vo => P2 vo
    | ValCons vc => P3 vc
    end
  >>
    match v with 
    | ValBase vb => c1 vb
    | ValObj vo  => c2 vo
    | ValCons vc => c3 vc
    end
  <<
    Q
  >>.
Proof.
  destruct v; auto.
Qed.

Lemma case_valbase_wp_p 
  {tags_t: Type}
  {State Exception Result: Type} 
  {PNull PBool PInteger PBit PInt PVarbit PString PTuple PRecord PSet PError PMatchKind PStruct PHeader PUnion PStack PEnumField PSenumField PSenum}
  {Q}
  {cNull cBool cInteger cBit cInt cVarbit cString cTuple cRecord cSet cError cMatchKind cStruct cHeader cUnion cStack cEnumField cSenumField}
  {cSenum: P4String.AList tags_t ValueBase -> @state_monad State Exception Result}
  v:
    (v = ValBaseNull -> << PNull >> cNull << Q >>) ->
    (forall b, v = ValBaseBool b -> << PBool b >> cBool b << Q >>) ->
    (forall i, v = ValBaseInteger i -> << PInteger i >> cInteger i << Q >>) ->
    (forall w v', v = ValBaseBit w v' -> << PBit w v' >> cBit w v' << Q >>) ->
    (forall w v', v = ValBaseInt w v' -> << PInt w v' >> cInt w v' << Q >>) ->
    (forall m w v', v = ValBaseVarbit m w v' -> << PVarbit m w v' >> cVarbit m w v' << Q >>) ->
    (forall s, v = ValBaseString s -> << PString s >> cString s << Q >>) ->
    (forall vs, v = ValBaseTuple vs -> << PTuple vs >> cTuple vs << Q >>) ->
    (forall entries, v = ValBaseRecord entries -> << PRecord entries >> cRecord entries << Q >>) ->
    (forall vs, v = ValBaseSet vs -> << PSet vs >> cSet vs << Q >>) ->
    (forall s, v = ValBaseError s -> << PError s >> cError s << Q >>) ->
    (forall s, v = ValBaseMatchKind s -> << PMatchKind s >> cMatchKind s << Q >>) ->
    (forall fields, v = ValBaseStruct fields -> << PStruct fields >> cStruct fields << Q >>) ->
    (forall fields is_valid, v = ValBaseHeader fields is_valid -> << PHeader fields is_valid >> cHeader fields is_valid << Q >>) ->
    (forall fields, v = ValBaseUnion fields -> << PUnion fields >> cUnion fields << Q >>) ->
    (forall headers sz nxt, v = ValBaseStack headers sz nxt -> << PStack headers sz nxt >> cStack headers sz nxt << Q >>) ->
    (forall tn en, v = ValBaseEnumField tn en -> << PEnumField tn en >> cEnumField tn en << Q >>) ->
    (forall tn en v', v = ValBaseSenumField tn en v' -> << PSenumField tn en v' >> cSenumField tn en v' << Q >>) ->
    (forall entries, v = ValBaseSenum entries -> << PSenum entries >> cSenum entries << Q >>) ->
  << 
    match v with 
    | ValBaseNull => PNull
    | ValBaseBool b => PBool b
    | ValBaseInteger i => PInteger i
    | ValBaseBit w v' => PBit w v'
    | ValBaseInt w v' => PInt w v'
    | ValBaseVarbit m w v' => PVarbit m w v'
    | ValBaseString s => PString s
    | ValBaseTuple vs => PTuple vs
    | ValBaseRecord entries => PRecord entries
    | ValBaseSet vs => PSet vs
    | ValBaseError s => PError s
    | ValBaseMatchKind s => PMatchKind s
    | ValBaseStruct fields => PStruct fields
    | ValBaseHeader fields is_valid => PHeader fields is_valid
    | ValBaseUnion fields => PUnion fields
    | ValBaseStack headers sz nxt => PStack headers sz nxt
    | ValBaseEnumField tn en => PEnumField tn en
    | ValBaseSenumField tn en v' => PSenumField tn en v'
    | ValBaseSenum entries => PSenum entries
    end
  >>
    match v with 
    | ValBaseNull => cNull
    | ValBaseBool b => cBool b
    | ValBaseInteger i => cInteger i
    | ValBaseBit w v' => cBit w v'
    | ValBaseInt w v' => cInt w v'
    | ValBaseVarbit m w v' => cVarbit m w v'
    | ValBaseString s => cString s
    | ValBaseTuple vs => cTuple vs
    | ValBaseRecord entries => cRecord entries
    | ValBaseSet vs => cSet vs
    | ValBaseError s => cError s
    | ValBaseMatchKind s => cMatchKind s
    | ValBaseStruct fields => cStruct fields
    | ValBaseHeader fields is_valid => cHeader fields is_valid
    | ValBaseUnion fields => cUnion fields
    | ValBaseStack headers sz nxt => cStack headers sz nxt
    | ValBaseEnumField tn en => cEnumField tn en
    | ValBaseSenumField tn en v => cSenumField tn en v
    | ValBaseSenum entries => cSenum entries
    end
  <<
    Q
  >>.
Proof.
  intros.
  destruct v; auto.
Qed.

Lemma case_valobj_wp_p 
  {tags_t: Type}
  {State Exception Result: Type} 
  {PParser PTable PControl PPackage PRuntime PFun PAction PPacket}
  {Q}
  {cParser cTable cControl cPackage cRuntime cFun cAction}
  {cPacket: list bool -> @state_monad State Exception Result}
  (vo: @ValueObject tags_t):
  
  (forall scope cparams params locals states, 
    vo = ValObjParser scope cparams params locals states -> 
    << PParser scope cparams params locals states >> 
      cParser scope cparams params locals states 
    << Q >>) ->
  (forall tbl, vo = ValObjTable tbl -> 
    << PTable tbl >> cTable tbl << Q >>) ->
  (forall scope cparams params locals body, 
    vo = ValObjControl scope cparams params locals body -> 
    << PControl scope cparams params locals body >> 
      cControl scope cparams params locals body 
    << Q >>) ->
  (forall args, vo = ValObjPackage args -> 
    << PPackage args >> cPackage args << Q >>) ->
  (forall loc obj_name, vo = ValObjRuntime loc obj_name -> 
    << PRuntime loc obj_name >> 
      cRuntime loc obj_name 
    << Q >>) ->
  (forall params impl, vo = ValObjFun params impl -> 
    << PFun params impl >> cFun params impl << Q >> ) ->
  (forall scope params body, vo = ValObjAction scope params body -> 
    << PAction scope params body >> cAction scope params body << Q >>) ->
  (forall bits, vo = ValObjPacket bits -> << PPacket bits >> cPacket bits << Q >>) ->
  <<
    match vo with 
    | ValObjParser scope cparams params locals states => PParser scope cparams params locals states
    | ValObjTable tbl => PTable tbl
    | ValObjControl scope cparams params locals body => PControl scope cparams params locals body
    | ValObjPackage args => PPackage args
    | ValObjRuntime loc obj_name => PRuntime loc obj_name
    | ValObjFun params impl => PFun params impl
    | ValObjAction scope params body => PAction scope params body
    | ValObjPacket bits => PPacket bits
    end
  >>
    match vo with 
    | ValObjParser scope cparams params locals states => cParser scope cparams params locals states
    | ValObjTable tbl => cTable tbl
    | ValObjControl scope cparams params locals body => cControl scope cparams params locals body
    | ValObjPackage args => cPackage args
    | ValObjRuntime loc obj_name => cRuntime loc obj_name
    | ValObjFun params impl => cFun params impl
    | ValObjAction scope params body => cAction scope params body
    | ValObjPacket bits => cPacket bits
    end
  << Q >>.
Proof.
  intros. 
  destruct vo; auto.
Qed.

Lemma case_valfuncimpl_wp_p 
  {tags_t: Type}
  {State Exception Result: Type}
  {PUser PExtern PBuiltin}
  {Q}
  {cUser cExtern}
  (cBuiltin: P4String.t tags_t -> ValueLvalue -> @state_monad State Exception Result)
  vfi :
  (forall scope body, vfi = ValFuncImplUser scope body -> << PUser scope body >> cUser scope body << Q >>) ->
  (forall name caller, vfi = ValFuncImplExtern name caller -> << PExtern name caller >> cExtern name caller << Q >>) ->
  (forall name caller, vfi = ValFuncImplBuiltin name caller -> << PBuiltin name caller >> cBuiltin name caller << Q >>) ->
  <<
    match vfi with 
    | ValFuncImplUser scope body => PUser scope body
    | ValFuncImplExtern name caller => PExtern name caller
    | ValFuncImplBuiltin name caller => PBuiltin name caller
    end
  >>
    match vfi with 
    | ValFuncImplUser scope body => cUser scope body
    | ValFuncImplExtern name caller => cExtern name caller
    | ValFuncImplBuiltin name caller => cBuiltin name caller
    end
  << Q >>.
Proof.
  intros. destruct vfi; auto.
Qed.

Ltac wp' := 
  match goal with
  | [ |- << _ >> match ?e with | ValFuncImplBuiltin _ _ => _ | _ => _ end << _ >> ] => eapply (case_valfuncimpl_wp_p e)
  | [ |- << _ >> match ?e with | ValBase _ => _ | _ => _ end << _ >> ] => eapply (case_val_wp_p e)
  | [ |- << _ >> match ?e with | ValBaseNull => _ | _ => _ end << _ >> ] => eapply (case_valbase_wp_p e)
  | [ |- << _ >> match ?e with | ValObjTable _ => _ | _ => _ end << _ >> ] => eapply (case_valobj_wp_p e)
  end.

Ltac wp_trans' := 
  repeat (intros; wp || wp'). 


Definition eval_control (c: @Declaration Info) : env_monad Info unit :=
  match c with 
  | DeclControl _ nme tparams params cparams locals body => eval_block _ NoInfo body
  | _ => state_fail (AssertError "declaration is not a control")
  end.

Lemma baby_ip_ingress : 
  << top >>
    eval_control MyIngress
  << fun _ _ => True >>.
Proof.
  Opaque mbind.
  unfold MyIngress, eval_control.
  unfold eval_block. simpl.
  unfold eval_expression. simpl.
  unfold eval_method_call.
  unfold Unpack.unpack_func.
  simpl.
  eapply strengthen_pre_p.
  wp_trans'.
  3: intros; eapply strengthen_pre_p; wp_trans'.
  7: intros; destruct r; wp_trans'.
  8: eapply strengthen_pre_p; wp_trans'.
  8: eapply case_valfuncimpl_wp_p. (* for some reason wp' doesn't work here? *)
  all: app_ex.
  all: try eapply strengthen_pre_p; wp_trans'; app_ex.

  4: unfold eval_builtin_func; wp_trans'; app_ex.

  all: unfold dummy_value, eval_is_valid, eval_set_bool.

  9:
    unfold eval_packet_func;
    unfold Unpack.unpack_packet;
    wp_trans';
    unfold mret, state_monad_inst; wp_trans'.

    (* at this point, the primitives are 
     * stack_pop, env_update, eval_cast, stack_push, stack_pop, eval_copy_out, 
     * env_lookup, eval_push_front, eval_pop_front, env_update, unpack_header, 
     * env_lookup, eval_copy_in, heap_lookup, stack_lookup 
     *)
Admitted.


(* some Props for reasoning about Environments, analogous to the MapsTo Prop for maps *)

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Import MNat := Environment.MNat.
Module Import MStr := Environment.MStr.

Inductive Stack_MapsTo : string -> loc -> stack -> Prop :=
  | InTopScope: 
    forall str l top, MapsTo str l top -> 
    forall stk, Stack_MapsTo str l (top :: stk)
  | InInnerScope: 
    forall str top,
    (forall l, ~ MapsTo str l top) -> 
    forall l' stk, Stack_MapsTo str l' stk -> 
    Stack_MapsTo str l' (top :: stk)  
  .

Lemma stack_lookup'_l: 
  forall str l stk, 
    stack_lookup' str stk = Some l -> 
    Stack_MapsTo str l stk.
Proof.
  intros.
  induction stk; [exfalso; inversion H|].
  (* destruct (find (elt:=l) str a). *)
  admit.
Admitted.

Lemma stack_lookup'_r: 
  forall str l stk, 
    Stack_MapsTo str l stk -> 
    stack_lookup' str stk = Some l.
Proof.
  intros.
  induction stk; inversion H; unfold stack_lookup'.
  - erewrite find_1.
    2: apply H3.
    trivial.
  - 
    assert ((forall loc0 : loc, ~ MapsTo str loc0 a) -> find str a = None).
    admit.
    specialize (H6 H4).
    rewrite H6.
    fold stack_lookup'.
    auto.
Admitted.

