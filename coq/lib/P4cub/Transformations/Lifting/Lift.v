From Coq Require Import Strings.String
  NArith.BinNat Arith.PeanoNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     P4cub.Syntax.IndPrincip
     P4cub.Transformations.Lifting.Statementize
     P4cub.Transformations.Lifting.LiftList
     Utils.ForallMap.
Import ListNotations Nat.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope exp_scope.
Local Open Scope stm_scope.

Inductive Lift_exp
  : Exp.t -> Exp.t -> list Exp.t -> Prop :=
| Lift_bool (b : bool) :
  Lift_exp (Exp.Bool b) (Exp.Bool b) []
| Lift_var t og x :
  Lift_exp (Exp.Var t og x) (Exp.Var t og x) []
| Lift_exprror err :
  Lift_exp (Exp.Error err) (Exp.Error err) []
| Lift_bit w n :
  Lift_exp (w `W n) (Exp.Var (Typ.Bit w) "lifted_bit" 0) [w `W n]
| Lift_int w z :
  Lift_exp (w `S z) (Exp.Var (Typ.Int w) "lifted_int" 0) [w `S z]
| Lift_varbit m w n :
  Lift_exp (Exp.VarBit m w n) (Exp.Var (Typ.VarBit m) "lifted_varbit" 0) [Exp.VarBit m w n]
| Lift_member t x e e' es :
  Lift_exp e e' es ->
  Lift_exp (Exp.Member t x e) (Exp.Member t x e') es
| Lift_uop t o e e' es :
  Lift_exp e e' es ->
  Lift_exp (Exp.Uop t o e) (Exp.Var t "lifted_uop" 0) (Exp.Uop t o e' :: es)
| Lift_slice hi lo e e' es :
  Lift_exp e e' es ->
  Lift_exp
    (Exp.Slice hi lo e)
    (Exp.Var (Typ.Bit (Npos hi - Npos lo + 1)%N) "lifted_slice" 0)
    (Exp.Slice hi lo e' :: es)
| Lift_cast t e e' es :
  Lift_exp e e' es ->
  Lift_exp (Exp.Cast t e) (Exp.Var t "lifted_cast" 0) (Exp.Cast t e' :: es)
| Lift_index t e1 e2 e1' e2' es1 es2 :
  Lift_exp e1 e1' es1 ->
  Lift_exp e2 e2' es2 ->
  Lift_exp
    (Exp.Index t e1 e2)
    (Exp.Index
       t
       (fst (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
       (snd (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2))))
    (snd (shift_couple shift_exp shift_exp e1' e2' es1 es2) ++ es1)
| Lift_bop t o e1 e2 e1' e2' es1 es2 :
  Lift_exp e1 e1' es1 ->
  Lift_exp e2 e2' es2 ->
  Lift_exp
    (Exp.Bop t o e1 e2)
    (Exp.Var t "lifted_bop" 0)
    (Exp.Bop
       t o
       (fst (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
       (snd (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
       :: snd (shift_couple shift_exp shift_exp e1' e2' es1 es2) ++ es1)
| Lift_lists ls es es' ess :
  Forall3 Lift_exp es es' ess ->
  Lift_exp
    (Exp.Lists ls es)
    (Exp.Var (typ_of_lists ls es) "lifted_lists" 0)
    (Exp.Lists ls (fst (shift_pairs shift_exp (combine es' ess)))
       :: concat (snd (shift_pairs shift_exp (combine es' ess)))).

Section LifteInduction.
  Variable P : Exp.t -> Exp.t -> list Exp.t -> Prop.

  Hypothesis HLift_bool : forall (b : bool), P (Exp.Bool b) (Exp.Bool b) [].

  Hypothesis HLift_var : forall t og x,
      P (Exp.Var t og x) (Exp.Var t og x) [].

  Hypothesis HLift_exprror : forall err,
      P (Exp.Error err) (Exp.Error err) [].
  
  Hypothesis HLift_bit : forall w n,
      P (w `W n) (Exp.Var (Typ.Bit w) "lifted_bit" 0) [w `W n].

  Hypothesis HLift_int : forall w z,
      P (w `S z) (Exp.Var (Typ.Int w) "lifted_int" 0) [w `S z].
  
  Hypothesis HLift_varbit : forall m w n,
      P (Exp.VarBit m w n) (Exp.Var (Typ.VarBit m) "lifted_varbit" 0) [Exp.VarBit m w n].

  Hypothesis HLift_member : forall t x e e' es,
      Lift_exp e e' es ->
      P e e' es ->
      P (Exp.Member t x e) (Exp.Member t x e') es.
  
  Hypothesis HLift_uop : forall t o e e' es,
      Lift_exp e e' es ->
      P e e' es ->
      P (Exp.Uop t o e) (Exp.Var t "lifted_uop" 0) (Exp.Uop t o e' :: es).
  
  Hypothesis HLift_slice : forall hi lo e e' es,
      Lift_exp e e' es ->
      P e e' es ->
      P
        (Exp.Slice hi lo e)
        (Exp.Var (Typ.Bit (Npos hi - Npos lo + 1)%N) "lifted_slice" 0)
        (Exp.Slice hi lo e' :: es).
  
  Hypothesis HLift_cast : forall t e e' es,
      Lift_exp e e' es ->
      P e e' es ->
      P (Exp.Cast t e) (Exp.Var t "lifted_cast" 0) (Exp.Cast t e' :: es).
  
  Hypothesis HLift_index : forall t e1 e2 e1' e2' es1 es2,
      Lift_exp e1 e1' es1 ->
      P e1 e1' es1 ->
      Lift_exp e2 e2' es2 ->
      P e2 e2' es2 ->
      P
        (Exp.Index t e1 e2)
        (Exp.Index
           t
           (fst (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
           (snd (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2))))
        (snd (shift_couple shift_exp shift_exp e1' e2' es1 es2) ++ es1).
  
  Hypothesis HLift_bop : forall t o e1 e2 e1' e2' es1 es2,
      Lift_exp e1 e1' es1 ->
      P e1 e1' es1 ->
      Lift_exp e2 e2' es2 ->
      P e2 e2' es2 ->
      P
        (Exp.Bop t o e1 e2)
        (Exp.Var t "lifted_bop" 0)
        (Exp.Bop
           t o
           (fst (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
           (snd (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2)))
           :: snd (shift_couple shift_exp shift_exp e1' e2' es1 es2) ++ es1).
  
  Hypothesis HLift_lists : forall ls es es' ess,
      Forall3 Lift_exp es es' ess ->
      Forall3 P es es' ess ->
      P
        (Exp.Lists ls es)
        (Exp.Var (typ_of_lists ls es) "lifted_lists" 0)
        (Exp.Lists ls (fst (shift_pairs shift_exp (combine es' ess)))
           :: concat (snd (shift_pairs shift_exp (combine es' ess)))).

  Definition custom_Lift_exp_ind : forall e e' es,
      Lift_exp e e' es -> P e e' es :=
    fix F e e' es hLift :=
      let fix F3 {es es' : list Exp.t} {ess : list (list Exp.t)}
            (h : Forall3 Lift_exp es es' ess)
        : Forall3 P es es' ess :=
        match h with
        | Forall3_nil _ => Forall3_nil _
        | Forall3_cons _ _ _ _ _ _ _ h ih
          => Forall3_cons _ _ _ _ _ _ _ (F _ _ _ h) (F3 ih)
        end in
      match hLift with
      | Lift_bool b => HLift_bool b
      | Lift_var x y z => HLift_var x y z
      | Lift_exprror e => HLift_exprror e
      | Lift_bit x y => HLift_bit x y
      | Lift_int x y => HLift_int x y
      | Lift_varbit m x y => HLift_varbit m x y
      | Lift_member t x _ _ _ h => HLift_member t x _ _ _ h (F _ _ _ h)
      | Lift_uop t o _ _ _ h => HLift_uop t o _ _ _ h (F _ _ _ h)
      | Lift_slice hi lo _ _ _ h => HLift_slice hi lo _ _ _ h (F _ _ _ h)
      | Lift_cast t _ _ _ h => HLift_cast t _ _ _ h (F _ _ _ h)
      | Lift_index t _ _ _ _ _ _ h1 h2
        => HLift_index t _ _ _ _ _ _ h1 (F _ _ _ h1) h2 (F _ _ _ h2)
      | Lift_bop x y _ _ _ _ _ _ h1 h2
        => HLift_bop x y _ _ _ _ _ _ h1 (F _ _ _ h1) h2 (F _ _ _ h2)
      | Lift_lists ls _ _ _ h => HLift_lists ls _ _ _ h (F3 h)
      end.
End LifteInduction.

Variant Lift_arg :
  Exp.arg -> Exp.arg -> list Exp.t -> Prop :=
  | Lift_pain e e' es :
    Lift_exp e e' es ->
    Lift_arg (PAIn e) (PAIn e') es
  | Lift_paout e e' es :
    Lift_exp e e' es ->
    Lift_arg (PAOut e) (PAOut e') es
  | Lift_painout e e' es :
    Lift_exp e e' es ->
    Lift_arg (PAInOut e) (PAInOut e') es.

Variant Lift_trns :
  Trns.t -> Trns.t -> list Exp.t ->  Prop :=
  | Lift_direct lbl :
    Lift_trns (Trns.Direct lbl) (Trns.Direct lbl) []
  | Lift_select e e' es d cases :
    Lift_exp e e' es ->
    Lift_trns
      (Trns.Select e d cases)
      (Trns.Select e' d cases) es.

Variant Lift_call :
  Call.t -> Call.t -> list Exp.t -> Prop :=
  | Lift_funct_none f τs :
    Lift_call (Call.Funct f τs None) (Call.Funct f τs None) []
  | Lift_method_none ext mtd τs :
    Lift_call
      (Call.Method ext mtd τs None)
      (Call.Method ext mtd τs None) []
  | Lift_funct_some f τs e e' es :
    Lift_exp e e' es ->
    Lift_call
      (Call.Funct f τs (Some e))
      (Call.Funct f τs (Some e')) es
  | Lift_method_some ext mtd τs e e' es :
    Lift_exp e e' es ->
    Lift_call
      (Call.Method ext mtd τs (Some e))
      (Call.Method ext mtd τs (Some e')) es
  | Lift_action_call a cargs cargs' ess :
    Lift_A_list shift_exp Lift_exp cargs cargs' ess ->
    Lift_call
      (Call.Action a cargs)
      (Call.Action a cargs')
      ess
  | Lift_inst_call x eargs :
    Lift_call (Call.Inst x eargs) (Call.Inst x eargs) [].

Inductive Lift_stm : Stm.t -> Stm.t -> Prop :=
| Lift_stmkip :
  Lift_stm Stm.Skip Stm.Skip
| Lift_exit :
  Lift_stm Stm.Exit Stm.Exit
| Lift_return_none :
  Lift_stm (Stm.Ret None) (Stm.Ret None)
| Lift_return_some e e' es :
  Lift_exp e e' es ->
  Lift_stm
    (Stm.Ret (Some e))
    (Unwind es (Stm.Ret (Some e')))
| Lift_transition e e' es :
  Lift_trns e e' es ->
  Lift_stm
    (Stm.Trans e)
    (Unwind es (Stm.Trans e'))
| Lift_asgn e1 e2 e1' e2' es1 es2 :
  Lift_exp e1 e1' es1 ->
  Lift_exp e2 e2' es2 ->
  Lift_stm
    (e1 `:= e2)
    (Unwind
       (snd (shift_couple shift_exp shift_exp e1' e2' es1 es2) ++ es1)
       (fst (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2))
          `:= snd (fst (shift_couple shift_exp shift_exp e1' e2' es1 es2))))
| Lift_setvalidity b e e' es :
  Lift_exp e e' es ->
  Lift_stm (Stm.SetValidity b e) (Unwind es (Stm.SetValidity b e'))
| Lift_invoke_none t :
  Lift_stm (Stm.Invoke None t) (Stm.Invoke None t)
| Lift_invoke e e' t es :
  Lift_exp e e' es ->
  Lift_stm
    (Stm.Invoke (Some e) t)
    (Unwind es (Stm.Invoke (Some e') t))
| Lift_app fk fk' fkes args args' argses :
  Lift_call fk fk' fkes ->
  Lift_A_list shift_arg Lift_arg args args' argses ->
  Lift_stm
    (Stm.App fk args)
    (Unwind
       (snd (shift_couple (fun c a => map (shift_arg c a)) shift_call args' fk' argses fkes)
          ++ argses)
       (Stm.App
           (snd (fst (shift_couple (fun c a => map (shift_arg c a)) shift_call args' fk' argses fkes)))
           (fst (fst (shift_couple (fun c a => map (shift_arg c a)) shift_call args' fk' argses fkes)))))
| Lift_stmeq s1 s2 s1' s2' :
  Lift_stm s1 s1' ->
  Lift_stm s2 s2' ->
  Lift_stm (s1 `; s2) (s1' `; s2')
| Lift_if e e' s1 s2 s1' s2' es :
  Lift_exp e e' es ->
  Lift_stm s1 s1' ->
  Lift_stm s2 s2' ->
  Lift_stm
    (`if e `then s1 `else s2)
    (Unwind
       es
       (`if e'
          `then shift_stm 0 (length es) s1'
          `else shift_stm 0 (length es) s2'))
| Lift_var_typ og t s s' :
  Lift_stm s s' ->
  Lift_stm
    (`let og := inl t `in s) (`let og := inl t `in s')
| Lift_var_exp og e e' s s' es :
  Lift_exp e e' es ->
  Lift_stm s s' ->
  Lift_stm
    (`let og := inr e `in s)
    (Unwind
       es
       (`let og := inr e' `in shift_stm 1 (length es) s')).

Section Liftlift.
  Lemma Lift_lift_exp : forall e e' es,
      Lift_exp e e' es -> lift_exp e = (e', es).
  Proof.
    intros e e' es h;
      induction h using custom_Lift_exp_ind;
      unravel;
      repeat let_destr_pair;
      repeat pair_fst_snd_eqns;
      auto.
    enough (map lift_exp es = combine es' ess) as h.
    { do 5 f_equal; assumption. }
    assert (h12 : length es = length es') by eauto using Forall3_length12.
    rewrite Forall3_map_1 with
      (R:=fun e e' es => e = (e', es))
      (f:=lift_exp) in H0.
    rewrite Forall3_Forall2_combine_r in H0.
    destruct H0 as [_ h].
    rewrite <- Forall2_eq.
    rewrite Forall2_forall_nth_error in h |- *.
    destruct h as [hlen h].
    split; try assumption.
    intros n [e Es] [e' es''] Hyp H'.
    firstorder.
  Qed.

  Local Hint Resolve Lift_lift_exp : core.

  Ltac apply_Lift_lift_exp :=
    match goal with
    | h: Lift_exp _ _ _
      |- _ => apply Lift_lift_exp in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Lift_lift_exp : core.

  Lemma Lift_lift_arg : forall arg arg' es,
      Lift_arg arg arg' es ->
      lift_arg arg = (arg', es).
  Proof.
    intros arg arg' es h; inv h; cbn; auto.
  Qed.

  Local Hint Resolve Lift_lift_arg : core.

  Ltac apply_Lift_lift_arg :=
    match goal with
    | h: Lift_arg _ _ _
      |- _ => apply Lift_lift_arg in h; rewrite h
    end.
  
  Local Hint Extern 5 => apply_Lift_lift_arg : core.

  Lemma Lift_lift_trns : forall pe pe' es,
      Lift_trns pe pe' es ->
      lift_trns pe = (pe',es).
  Proof.
    intros pe pe' es h; inv h; unravel; auto.
  Qed.

  Local Hint Resolve Lift_lift_trns : core.
  
  Ltac apply_Lift_lift_trns :=
      match goal with
      | h: Lift_trns _ _ _
        |- _ => apply Lift_lift_trns in h; rewrite h
      end.

  Local Hint Extern 5 => apply_Lift_lift_trns : core.

  Lemma Forall3_Lift_lift_exp : forall es es' ess,
      Forall3 Lift_exp es es' ess ->
      map lift_exp es = combine es' ess.
  Proof.
    refine (Forall3_LiftA_map_lifta _ _ _). auto.
  Qed.

  Ltac apply_Forall3_Lift_lift_exp :=
    match goal with
    | h : Forall3 Lift_exp _ _ _
      |- _ => apply Forall3_Lift_lift_exp in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Forall3_Lift_lift_exp : core.
  
  Lemma Lift_lift_call : forall fk fk' es,
      Lift_call fk fk' es ->
      lift_call fk = (fk', es).
  Proof.
    intros fk fk' es h; inv h; cbn; auto.
    let_destr_pair.
    eapply Lift_A_list_lift_A_list with (lifta:=lift_exp) in H; auto.
    unfold lift_exp_list.
    pair_fst_snd_eqns. reflexivity.
  Qed.

  Local Hint Resolve Lift_lift_call : core.

  Ltac apply_Lift_lift_call :=
      match goal with
      | h: Lift_call _ _ _
        |- _ => apply Lift_lift_call in h; rewrite h
      end.

  Local Hint Extern 5 => apply_Lift_lift_call : core.
  
  Lemma Forall3_Lift_lift_arg : forall args args' ess,
      Forall3 Lift_arg args args' ess ->
      map lift_arg args = combine args' ess.
  Proof.
    refine (Forall3_LiftA_map_lifta _ _ _). auto.
  Qed.

  Ltac apply_Forall3_Lift_lift_arg :=
    match goal with
    | h : Forall3 Lift_arg _ _ _
      |- _ => apply Forall3_Lift_lift_arg in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Forall3_Lift_lift_arg : core.

  Lemma Lift_lift_stm : forall s s',
      Lift_stm s s' -> lift_stm s = s'.
  Proof.
    intros s s' h; induction h; unravel; subst;
      repeat let_destr_pair; auto.
    apply Lift_lift_call in H.
    apply Lift_A_list_lift_A_list with (lifta:=lift_arg) in H0; auto.
    do 2 pair_fst_snd_eqns. reflexivity.
  Qed.
End Liftlift.

Section liftLift.
  Local Hint Constructors Lift_exp : core.
  
  Lemma lift_Lift_exp : forall e,
    Lift_exp e (fst (lift_exp e)) (snd (lift_exp e)).
  Proof.
    intro e; induction e using custom_exp_ind; cbn;
      repeat let_destr_pair; unravel; auto.
    - constructor. assumption.
    - rewrite <- combine_map_fst_snd with (l:=map lift_exp es).
      constructor.
      do 2 rewrite <- Forall3_map_23.
      rewrite Forall3_Forall_123. assumption.
  Qed.

  Local Hint Resolve lift_Lift_exp : core.
  
  Corollary lift_Lift_exp_aux : forall e e' es,
      lift_exp e = (e', es) -> Lift_exp e e' es.
  Proof.
    intros; pair_fst_snd_eqns; auto.
  Qed.

  Local Hint Resolve lift_Lift_exp_aux : core.
  Local Hint Constructors Lift_arg : core.
  
  Lemma lift_Lift_arg : forall arg,
      Lift_arg arg (fst (lift_arg arg)) (snd (lift_arg arg)).
  Proof.
    intros [e | e | e]; unravel;
      let_destr_pair; cbn; auto.
  Qed.

  Local Hint Resolve lift_Lift_arg : core.

  Corollary lift_Lift_arg_aux : forall arg arg' es,
      lift_arg arg = (arg', es) ->
      Lift_arg arg arg' es.
  Proof.
    intros; pair_fst_snd_eqns; auto.
  Qed.

  Local Hint Resolve lift_Lift_arg_aux : core.
  Local Hint Constructors Lift_trns : core.
  
  Lemma lift_Lift_trns : forall e,
      Lift_trns e (fst (lift_trns e)) (snd (lift_trns e)).
  Proof.
    intros []; unravel;
      try let_destr_pair; cbn; auto.
  Qed.

  Local Hint Resolve lift_Lift_trns : core.

  Corollary lift_Lift_trns_aux : forall e e' es,
      lift_trns e = (e', es) ->
      Lift_trns e e' es.
  Proof.
    intros; pair_fst_snd_eqns; auto.
  Qed.

  Local Hint Resolve lift_Lift_trns_aux : core.
  Local Hint Constructors Lift_call : core.
  Local Hint Resolve lift_A_list_Lift_A_list : core.
  
  Lemma lift_Lift_call : forall fk,
      Lift_call fk (fst (lift_call fk)) (snd (lift_call fk)).
  Proof.
    intros [f ts [e |] | a cs | extrn mthd ts [e |] | ? ?];
      unravel; try let_destr_pair; cbn; eauto using lift_A_list_Lift_A_list.
  Qed.

  Local Hint Resolve lift_Lift_call : core.

  Lemma lift_Lift_call_aux : forall fk fk' es,
      lift_call fk = (fk', es) ->
      Lift_call fk fk' es.
  Proof.
    intros; pair_fst_snd_eqns; auto.
  Qed.

  Local Hint Resolve lift_Lift_call_aux : core.
  Local Hint Constructors Lift_stm : core.

  Lemma lift_Lift_stm : forall s,
      Lift_stm s (lift_stm s).
  Proof.
    intro s; induction s; unravel;
      repeat let_destr_pair;
      eauto using lift_A_list_Lift_A_list.
    - destruct e as [e |];
        try let_destr_pair; auto.
    - destruct lhs as [e |];
        try let_destr_pair; eauto.
    - destruct init as [t | e];
        try let_destr_pair; auto.
  Qed.
End liftLift.
