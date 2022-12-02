From Coq Require Import Strings.String
  NArith.BinNat Arith.PeanoNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     P4cub.Syntax.IndPrincip
     P4cub.Transformations.Lifting.Statementize
     Utils.ForallMap.
Import ListNotations AllCubNotations Nat.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Goal forall e es,
    shift_pairs shift_e [(e,es)] = [(e,es)].
Proof.
  intros; cbn; rewrite shift_e_0 , shift_elist_0. reflexivity.
Qed.

Goal forall e1 e2 es1 es2,
    shift_pairs shift_e [(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es2) (length es1)) e2,
         shift_list shift_e (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0.
  reflexivity.
Qed.

Goal forall e1 e2 e3 es1 es2 es3,
    shift_pairs shift_e [(e3,es3);(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es3) (length es2 + length es1)) e3,
            shift_list shift_e (Shifter 0 (length es2 + length es1)) es3);
       (shift_e (Shifter 0 (length es3)) (shift_e (Shifter (length es2) (length es1)) e2),
         shift_list shift_e (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es3 + length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0, shift_e_add.
  reflexivity.
Qed.
       
Inductive Lift_e
  : Expr.e -> Expr.e -> list Expr.e -> Prop :=
| Lift_bool (b : bool) :
  Lift_e b b []
| Lift_var t og x :
  Lift_e (Expr.Var t og x) (Expr.Var t og x) []
| Lift_error err :
  Lift_e (Expr.Error err) (Expr.Error err) []
| Lift_bit w n :
  Lift_e (w `W n) (Expr.Var (Expr.TBit w) "" 0) [w `W n]
| Lift_int w z :
  Lift_e (w `S z) (Expr.Var (Expr.TInt w) "" 0) [w `S z]
| Lift_varbit w n :
  Lift_e (Expr.VarBit w n) (Expr.Var (Expr.TVarBit w) "" 0) [Expr.VarBit w n]
| Lift_member t x e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Member t x e) (Expr.Member t x e') es
| Lift_uop t o e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Uop t o e) (Expr.Var t "" 0) (Expr.Uop t o e' :: es)
| Lift_slice hi lo e e' es :
  Lift_e e e' es ->
  Lift_e
    (Expr.Slice hi lo e)
    (Expr.Var (Expr.TBit (Npos hi - Npos lo + 1)%N) "" 0)
    (Expr.Slice hi lo e' :: es)
| Lift_cast t e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Cast t e) (Expr.Var t "" 0) (Expr.Cast t e' :: es)
| Lift_index t e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Index t e1 e2)
    (Expr.Index
       t
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2'))
    (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
| Lift_bop t o e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Bop t o e1 e2)
    (Expr.Var t "" 0)
    (Expr.Bop
       t o
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2')
       :: shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
| Lift_lists ls es es' ess :
  Forall3 Lift_e es es' ess ->
  Lift_e
    (Expr.Lists ls es)
    (Expr.Var (t_of_lists ls es) "" 0)
    (Expr.Lists ls (map fst (shift_pairs shift_e (combine es' ess)))
       :: concat (map snd (shift_pairs shift_e (combine es' ess)))).

Section LifteInduction.
  Variable P : Expr.e -> Expr.e -> list Expr.e -> Prop.

  Hypothesis HLift_bool : forall (b : bool), P b b [].

  Hypothesis HLift_var : forall t og x,
      P (Expr.Var t og x) (Expr.Var t og x) [].

  Hypothesis HLift_error : forall err,
      P (Expr.Error err) (Expr.Error err) [].
  
  Hypothesis HLift_bit : forall w n,
      P (w `W n) (Expr.Var (Expr.TBit w) "" 0) [w `W n].

  Hypothesis HLift_int : forall w z,
      P (w `S z) (Expr.Var (Expr.TInt w) "" 0) [w `S z].
  
  Hypothesis HLift_varbit : forall w n,
      P (Expr.VarBit w n) (Expr.Var (Expr.TVarBit w) "" 0) [Expr.VarBit w n].

  Hypothesis HLift_member : forall t x e e' es,
      Lift_e e e' es ->
      P e e' es ->
      P (Expr.Member t x e) (Expr.Member t x e') es.
  
  Hypothesis HLift_uop : forall t o e e' es,
      Lift_e e e' es ->
      P e e' es ->
      P (Expr.Uop t o e) (Expr.Var t "" 0) (Expr.Uop t o e' :: es).
  
  Hypothesis HLift_slice : forall hi lo e e' es,
      Lift_e e e' es ->
      P e e' es ->
      P
        (Expr.Slice hi lo e)
        (Expr.Var (Expr.TBit (Npos hi - Npos lo + 1)%N) "" 0)
        (Expr.Slice hi lo e' :: es).
  
  Hypothesis HLift_cast : forall t e e' es,
      Lift_e e e' es ->
      P e e' es ->
      P (Expr.Cast t e) (Expr.Var t "" 0) (Expr.Cast t e' :: es).
  
  Hypothesis HLift_index : forall t e1 e2 e1' e2' es1 es2,
      Lift_e e1 e1' es1 ->
      P e1 e1' es1 ->
      Lift_e e2 e2' es2 ->
      P e2 e2' es2 ->
      P
        (Expr.Index t e1 e2)
        (Expr.Index
           t
           (shift_e (Shifter 0 (length es2)) e1')
           (shift_e (Shifter (length es2) (length es1)) e2'))
        (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1).
  
  Hypothesis HLift_bop : forall t o e1 e2 e1' e2' es1 es2,
      Lift_e e1 e1' es1 ->
      P e1 e1' es1 ->
      Lift_e e2 e2' es2 ->
      P e2 e2' es2 ->
      P
        (Expr.Bop t o e1 e2)
        (Expr.Var t "" 0)
        (Expr.Bop
           t o
           (shift_e (Shifter 0 (length es2)) e1')
           (shift_e (Shifter (length es2) (length es1)) e2')
           :: shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1).
  
  Hypothesis HLift_lists : forall ls es es' ess,
      Forall3 Lift_e es es' ess ->
      Forall3 P es es' ess ->
      P
        (Expr.Lists ls es)
        (Expr.Var (t_of_lists ls es) "" 0)
        (Expr.Lists ls (map fst (shift_pairs shift_e (combine es' ess)))
           :: concat (map snd (shift_pairs shift_e (combine es' ess)))).

  Definition custom_Lift_e_ind : forall e e' es,
      Lift_e e e' es -> P e e' es :=
    fix F e e' es hLift :=
      let fix F3 {es es' : list Expr.e} {ess : list (list Expr.e)}
            (h : Forall3 Lift_e es es' ess)
        : Forall3 P es es' ess :=
        match h with
        | Forall3_nil _ => Forall3_nil _
        | Forall3_cons _ _ _ _ _ _ _ h ih
          => Forall3_cons _ _ _ _ _ _ _ (F _ _ _ h) (F3 ih)
        end in
      match hLift with
      | Lift_bool b => HLift_bool b
      | Lift_var x y z => HLift_var x y z
      | Lift_error e => HLift_error e
      | Lift_bit x y => HLift_bit x y
      | Lift_int x y => HLift_int x y
      | Lift_varbit x y => HLift_varbit x y
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
  Expr.arg -> Expr.arg -> list Expr.e -> Prop :=
  | Lift_pain e e' es :
    Lift_e e e' es ->
    Lift_arg (PAIn e) (PAIn e') es
  | Lift_paout e e' es :
    Lift_e e e' es ->
    Lift_arg (PAOut e) (PAOut e') es
  | Lift_painout e e' es :
    Lift_e e e' es ->
    Lift_arg (PAInOut e) (PAInOut e') es.

Variant Lift_trans :
  Parser.trns -> Parser.trns -> list Expr.e ->  Prop :=
  | Lift_direct lbl :
    Lift_trans (Parser.Direct lbl) (Parser.Direct lbl) []
  | Lift_select e e' es d cases :
    Lift_e e e' es ->
    Lift_trans
      (Parser.Select e d cases)
      (Parser.Select e' d cases) es.

Variant Lift_fun_kind :
  Stmt.fun_kind -> Stmt.fun_kind -> list Expr.e -> Prop :=
  | Lift_funct_none f τs :
    Lift_fun_kind (Stmt.Funct f τs None) (Stmt.Funct f τs None) []
  | Lift_method_none ext mtd τs :
    Lift_fun_kind
      (Stmt.Method ext mtd τs None)
      (Stmt.Method ext mtd τs None) []
  | Lift_funct_some f τs e e' es :
    Lift_e e e' es ->
    Lift_fun_kind
      (Stmt.Funct f τs (Some e))
      (Stmt.Funct f τs (Some e')) es
  | Lift_method_some ext mtd τs e e' es :
    Lift_e e e' es ->
    Lift_fun_kind
      (Stmt.Method ext mtd τs (Some e))
      (Stmt.Method ext mtd τs (Some e')) es
  | Lift_action_call a cargs cargs' ess :
    Forall3 Lift_e cargs cargs' ess ->
    Lift_fun_kind
      (Stmt.Action a cargs)
      (Stmt.Action a (map fst (shift_pairs shift_e (combine cargs' ess))))
      (concat (map snd (shift_pairs shift_e (combine cargs' ess)))).

Inductive Lift_s : Stmt.s -> Stmt.s -> Prop :=
| Lift_skip :
  Lift_s Stmt.Skip Stmt.Skip
| Lift_exit :
  Lift_s Stmt.Exit Stmt.Exit
| Lift_invoke t :
  Lift_s (Stmt.Invoke t) (Stmt.Invoke t)
| Lift_return_none :
  Lift_s (Stmt.Return None) (Stmt.Return None)
| Lift_return_some e e' es :
  Lift_e e e' es ->
  Lift_s
    (Stmt.Return (Some e))
    (Unwind es (Stmt.Return (Some e')))
| Lift_transition e e' es :
  Lift_trans e e' es ->
  Lift_s
    (Stmt.Transition e)
    (Unwind es (Stmt.Transition e'))
| Lift_asgn e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_s
    (e1 `:= e2)
    (Unwind
       (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
       (shift_e (Shifter 0 (length es2)) e1'
          `:= shift_e (Shifter (length es2) (length es1)) e2'))
| Lift_call fk fk' fkes args args' argsess :
  Lift_fun_kind fk fk' fkes ->
  Forall3 Lift_arg args args' argsess ->
  Lift_s
    (Stmt.Call fk args)
    (Unwind
       (shift_list shift_e (Shifter 0 (length (concat argsess))) fkes
          ++ concat (map snd (shift_pairs shift_arg (combine args' argsess))))
       (Stmt.Call
           (shift_fun_kind (Shifter (length fkes) (length (concat argsess))) fk')
           (map (shift_arg $ Shifter 0 (length fkes))
              (map fst (shift_pairs shift_arg (combine args' argsess))))))
| Lift_apply x exts args args' argsess :
  Forall3 Lift_arg args args' argsess ->
  Lift_s
    (Stmt.Apply x exts args)
    (Unwind
       (concat (map snd (shift_pairs shift_arg (combine args' argsess))))
       (Stmt.Apply x exts
          (map fst (shift_pairs shift_arg (combine args' argsess)))))
| Lift_seq s1 s2 s1' s2' :
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s (s1 `; s2) (s1' `; s2')
| Lift_if e e' s1 s2 s1' s2' es :
  Lift_e e e' es ->
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s
    (If e Then s1 Else s2)
    (Unwind
       es
       (If e'
          Then shift_s (Shifter 0 (length es)) s1'
          Else shift_s (Shifter 0 (length es)) s2'))
| Lift_var_typ og t s s' :
  Lift_s s s' ->
  Lift_s (Stmt.Var og (inl t) s) (Stmt.Var og (inl t) s')
| Lift_var_exp og e e' s s' es :
  Lift_e e e' es ->
  Lift_s s s' ->
  Lift_s
    (Stmt.Var og (inr e) s)
    (Unwind
       es
       (Stmt.Var og (inr e') (shift_s (Shifter 1 (length es)) s'))).

Ltac destr_call_pair f :=
  match goal with
  | |- context [f ?a]
    => destruct (f a) as [? ?] eqn:?; subst
  end.
    
Ltac destr_lift_e := destr_call_pair lift_e.

Ltac destr_lift_arg := destr_call_pair lift_arg.

Ltac destr_lift_e_list := destr_call_pair lift_e_list.

Ltac destr_lift_trans := destr_call_pair lift_trans.

Ltac destr_lift_args := destr_call_pair lift_args.

Section Liftlift.
  Lemma Lift_lift_e : forall e e' es,
      Lift_e e e' es -> lift_e e = (e', es).
  Proof.
    intros e e' es h;
      induction h using custom_Lift_e_ind;
      unravel;
      repeat destr_lift_e;
      repeat match goal with
        | h: (_, _) = (_, _) |- _ => inv h
        end; auto.
    destruct (split (shift_pairs shift_e (map lift_e es)))
      as [es'' les] eqn:hsplit.
    rewrite split_map in hsplit. inv hsplit.
    enough (map lift_e es = combine es' ess) as h.
    { do 5 f_equal; assumption. }
    assert (h12 : length es = length es') by eauto using Forall3_length12.
    rewrite Forall3_map_1 with
      (R:=fun e e' es => e = (e', es))
      (f:=lift_e) in H0.
    rewrite Forall3_Forall2_combine_r in H0.
    destruct H0 as [_ h].
    rewrite <- Forall2_eq.
    rewrite Forall2_forall_nth_error in h |- *.
    destruct h as [hlen h].
    split; try assumption.
    intros n [e Es] [e' es''] Hyp H'.
    firstorder.
  Qed.

  Local Hint Resolve Lift_lift_e : core.

  Ltac apply_Lift_lift_e :=
    match goal with
    | h: Lift_e _ _ _
      |- _ => apply Lift_lift_e in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Lift_lift_e : core.

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

  Lemma Lift_lift_trans : forall pe pe' es,
      Lift_trans pe pe' es ->
      lift_trans pe = (pe',es).
  Proof.
    intros pe pe' es h; inv h; unravel; auto.
  Qed.

  Local Hint Resolve Lift_lift_trans : core.
  
  Ltac apply_Lift_lift_trans :=
      match goal with
      | h: Lift_trans _ _ _
        |- _ => apply Lift_lift_trans in h; rewrite h
      end.

  Local Hint Extern 5 => apply_Lift_lift_trans : core.

  Lemma Forall3_Lift_lift_e : forall es es' ess,
      Forall3 Lift_e es es' ess ->
      map lift_e es = combine es' ess.
  Proof.
    intros es es' ess h;
      induction h; cbn; f_equal; auto.
  Qed.

  Ltac apply_Forall3_Lift_lift_e :=
    match goal with
    | h : Forall3 Lift_e _ _ _
      |- _ => apply Forall3_Lift_lift_e in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Forall3_Lift_lift_e : core.
  
  Lemma Lift_lift_fun_kind : forall fk fk' es,
      Lift_fun_kind fk fk' es ->
      lift_fun_kind fk = (fk', es).
  Proof.
    intros fk fk' es h; inv h; unravel; auto.
    unfold lift_e_list.
    destruct (split (shift_pairs shift_e $ map lift_e cargs))
      as [es les] eqn:hs.
    rewrite split_map in hs; unravel in hs; inv hs.
    auto.
  Qed.

  Local Hint Resolve Lift_lift_fun_kind : core.

  Ltac apply_Lift_lift_fun_kind :=
      match goal with
      | h: Lift_fun_kind _ _ _
        |- _ => apply Lift_lift_fun_kind in h; rewrite h
      end.

  Local Hint Extern 5 => apply_Lift_lift_fun_kind : core.
  
  Lemma Forall3_Lift_lift_arg : forall args args' ess,
      Forall3 Lift_arg args args' ess ->
      map lift_arg args = combine args' ess.
  Proof.
    intros es es' ess h;
      induction h; cbn; f_equal; auto.
  Qed.

  Ltac apply_Forall3_Lift_lift_arg :=
    match goal with
    | h : Forall3 Lift_arg _ _ _
      |- _ => apply Forall3_Lift_lift_arg in h; rewrite h
    end.

  Local Hint Extern 5 => apply_Forall3_Lift_lift_arg : core.

  Lemma Lift_lift_s : forall s s',
      Lift_s s s' -> lift_s s = s'.
  Proof.
    intros s s' h; induction h; unravel; subst; auto.
    - apply_Lift_lift_fun_kind.
      unfold lift_args.
      destruct
        (split (shift_pairs shift_arg $ map lift_arg args))
        as [Args les] eqn:hsplit.
      rewrite split_map in hsplit.
      unravel in *; inv hsplit.
      rewrite sublist.length_concat.
      rewrite shift_pairs_inner_length.
      rewrite <- sublist.length_concat.
      assert (hlen12 : length args = length args')
        by eauto using Forall3_length12.
      assert (hlen13 : length args = length argsess)
        by eauto using Forall3_length13.
      assert (hlen23 : length args' = length argsess)
        by eauto using Forall3_length23.
      apply_Forall3_Lift_lift_arg.
      repeat f_equal; auto using map_snd_combine.
    - unfold lift_args.
      destruct
        (split (shift_pairs shift_arg $ map lift_arg args))
        as [Args les] eqn:hsplit.
      rewrite split_map in hsplit.
      unravel in *; inv hsplit. auto.
  Qed.
End Liftlift.

Section liftLift.
  Local Hint Constructors Lift_e : core.
  
  Lemma lift_Lift_e : forall e,
    Lift_e e (fst (lift_e e)) (snd (lift_e e)).
  Proof.
    intro e; induction e using custom_e_ind; cbn;
      repeat destr_lift_e; cbn in *; auto.
    - constructor. assumption.
    - destruct
        (split (shift_pairs shift_e $ map lift_e exps)) as [es' les] eqn:hes.
      rewrite split_map in hes.
      unravel in *. inv hes.
      assert (h: Forall3
                   Lift_e
                   exps
                   (map fst (map lift_e exps))
                   (map snd (map lift_e exps))).
      { clear l.
        rewrite Forall_forall in H.
        rewrite Forall3_forall.
        repeat rewrite map_length.
        repeat split; try reflexivity.
        intros n e e' es he he' hes.
        pose proof H _ (nth_error_In _ _ he) as h.
        do 2 rewrite nth_error_map in he',hes.
        rewrite he in he',hes.
        cbn in he',hes.
        inv he'; inv hes.
        assumption. }
      rewrite <- combine_map_fst_snd
        with (l:=map lift_e exps). auto.
  Qed.

  Local Hint Resolve lift_Lift_e : core.

  Ltac solve_aux h :=
    pose proof f_equal fst h as h1;
    pose proof f_equal snd h as h2;
    cbn in *; subst; auto.
  
  Corollary lift_Lift_e_aux : forall e e' es,
      lift_e e = (e', es) -> Lift_e e e' es.
  Proof.
    intros e e' es h; solve_aux h.
  Qed.

  Local Hint Resolve lift_Lift_e_aux : core.
  Local Hint Constructors Lift_arg : core.
  
  Lemma lift_Lift_arg : forall arg,
      Lift_arg arg (fst (lift_arg arg)) (snd (lift_arg arg)).
  Proof.
    intros [e | e | e]; unravel;
      destr_lift_e; cbn; auto.
  Qed.

  Local Hint Resolve lift_Lift_arg : core.

  Corollary lift_Lift_arg_aux : forall arg arg' es,
      lift_arg arg = (arg', es) ->
      Lift_arg arg arg' es.
  Proof.
    intros arg arg' es h; solve_aux h.
  Qed.

  Local Hint Resolve lift_Lift_arg_aux : core.
  Local Hint Constructors Lift_trans : core.
  
  Lemma lift_Lift_trans : forall e,
      Lift_trans e (fst (lift_trans e)) (snd (lift_trans e)).
  Proof.
    intros []; unravel;
      try destr_lift_e; cbn; auto.
  Qed.

  Local Hint Resolve lift_Lift_trans : core.

  Corollary lift_Lift_trans_aux : forall e e' es,
      lift_trans e = (e', es) ->
      Lift_trans e e' es.
  Proof.
    intros e e' es h; solve_aux h.
  Qed.

  Local Hint Resolve lift_Lift_trans_aux : core.
  Local Hint Constructors Lift_fun_kind : core.

  Lemma lift_Lift_fun_kind : forall fk,
      Lift_fun_kind fk (fst (lift_fun_kind fk)) (snd (lift_fun_kind fk)).
  Proof.
    intros [f ts [e |] | a cs | extrn mthd ts [e |]];
      unravel; try destr_lift_e; cbn; auto.
    destr_lift_e_list.
    unfold lift_e_list in Heqp.
    destruct (split (shift_pairs shift_e $ map lift_e cs))
      as [es ees] eqn:hsplit.
    unravel in *.
    rewrite split_map in hsplit.
    inv hsplit; inv Heqp.
    rewrite <- combine_map_fst_snd
      with (l:=map lift_e cs).
    constructor.
    rewrite Forall3_forall.
    repeat rewrite map_length.
    repeat (split; try reflexivity).
    intros n e e' es he he' hes.
    do 2 rewrite nth_error_map in he',hes.
    rewrite he in he',hes. cbn in *.
    inv he'; inv hes. auto.
  Qed.

  Local Hint Resolve lift_Lift_fun_kind : core.

  Lemma lift_Lift_fun_kind_aux : forall fk fk' es,
      lift_fun_kind fk = (fk', es) ->
      Lift_fun_kind fk fk' es.
  Proof.
    intros fk fk' es h. solve_aux h.
  Qed.

  Local Hint Resolve lift_Lift_fun_kind_aux : core.
  Local Hint Constructors Lift_s : core.

  Lemma lift_Lift_stmt : forall s,
      Lift_s s (lift_s s).
  Proof.
    intro s; induction s; unravel;
      try destr_lift_trans;
      repeat destr_lift_e;
      try destr_call_pair lift_fun_kind;
      try destr_lift_args;
      auto.
    - destruct e as [e |];
        try destr_lift_e; auto.
    - unfold lift_args in Heqp0.
      destruct (split (shift_pairs shift_arg $ map lift_arg args))
        as [args' les] eqn:hsplit.
      unravel in *.
      rewrite split_map in hsplit.
      inv hsplit; inv Heqp0.
      rewrite sublist.length_concat.
      rewrite shift_pairs_inner_length.
      rewrite <- sublist.length_concat.
      rewrite <- combine_map_fst_snd
        with (l := map lift_arg args) at 4.
      rewrite <- combine_map_fst_snd
        with (l := map lift_arg args) at 2.
      constructor; auto.
      rewrite Forall3_forall.
      repeat rewrite map_length.
      repeat (split; try reflexivity).
      intros n arg arg' es harg harg' hes.
      do 2 rewrite nth_error_map in harg',hes.
      unfold Expr.arg in *.
      rewrite harg in harg',hes; cbn in *.
      inv harg'; inv hes. auto.
    - unfold lift_args in Heqp.
      destruct
        (split (shift_pairs shift_arg $ map lift_arg args))
        as [args' es] eqn:hsplit.
      rewrite split_map in hsplit.
      unravel in *.
      inv hsplit; inv Heqp.
      rewrite <- combine_map_fst_snd
        with (l := map lift_arg args).
      constructor.
      rewrite Forall3_forall.
      repeat rewrite map_length.
      repeat (split; try reflexivity).
      intros n arg arg' es harg harg' hes.
      do 2 rewrite nth_error_map in harg',hes.
      unfold Expr.arg in *.
      rewrite harg in harg',hes; cbn in *.
      inv harg'; inv hes. auto.
    - destruct expr as [t | e];
        try destr_lift_e; auto.
  Qed.
End liftLift.
