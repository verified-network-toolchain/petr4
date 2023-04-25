Require Import Coq.Strings.String Coq.NArith.BinNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     Utils.ForallMap
     Utils.VecUtil.
Import ListNotations.
From Equations Require Import Equations.
Require Poulet4.Utils.ProdN.

Open Scope nat_scope.
Open Scope string_scope.

Section ShiftPairs.
  Import ProdN.ProdNNotations.
  Import Vec.VectorNotations.
  Local Open Scope prodn_scope.

  Polymorphic Universes a.
  
  Polymorphic Equations prodn_shift_pairs :
    forall {n : nat} {AS : Vec.t Type@{a} n},
      ProdN.t (Vec.map shifter AS) ->
      ProdN.t AS -> Vec.t (list Exp.t) n ->
      ProdN.t AS * Vec.t (list Exp.t) n := {
      prodn_shift_pairs [] [] []%vector := ([], []%vector);
      prodn_shift_pairs (f :: fs) (a :: p) (es :: ess)%vector :=
        let m := vec_sum $ Vec.map (length (A:=Exp.t)) ess in
        let '(p', v') := prodn_shift_pairs fs p ess in
        (f (length es) m a ::
           ProdN.map_uni2 0 (length es) fs p',
          (shift_list shift_exp 0 m es :: v')%vector)
    }.

  Polymorphic Lemma prodn_shift_pairs_inner_length :
    forall {n : nat} {AS : Vec.t Type@{a} n}
      (fs : ProdN.t (Vec.map shifter AS))
      (p : ProdN.t AS) (v : Vec.t (list Exp.t) n),
      Vec.map (length (A:=Exp.t)) (snd (prodn_shift_pairs fs p v))
      = Vec.map (length (A:=Exp.t)) v.
  Proof using.
    intros n AS fs p v.
    funelim (prodn_shift_pairs fs p v); unravel in *.
    - reflexivity.
    - rewrite prodn_shift_pairs_equation_2. cbn.
      destruct (prodn_shift_pairs fs p ess) as [p' v'] eqn:hpsp.
      unravel.
      rewrite shift_list_length.
      f_equal. assumption.
  Qed.

  Section ShiftCouple.
    Polymorphic Context {A : Type@{a}}.
    Variables fa : shifter A.

    Polymorphic Definition vec_shift_pairs
      {n : nat} (v : Vec.t A n) (ess : Vec.t (list Exp.t) n)
      : Vec.t A n * Vec.t (list Exp.t) n :=
      prod_map_fst ProdN.to_vec $
        prodn_shift_pairs
        (AS:=vec_rep n A) (ProdN.rep_param fa n) (ProdN.of_vec v) ess.
    
    Polymorphic Definition shift_pairs
      (l : list (A * list Exp.t)) : list A * list (list Exp.t) :=
      let '(v,ess) := vec_unzip $ Vec.of_list l in
      prod_map_fst Vec.to_list $ prod_map_snd Vec.to_list $ vec_shift_pairs v ess.

    Polymorphic Lemma shift_pairs_lengths : forall l,
        length (fst (shift_pairs l)) = length l
        /\ length (snd (shift_pairs l)) = length l.
    Proof using.
      intro l; unfold shift_pairs; unravel.
      destruct (vec_unzip (Vec.of_list l)) as [v ess] eqn:hl.
      rewrite fst_prod_map_fst, snd_prod_map_fst,
        fst_prod_map_snd, snd_prod_map_snd.
      do 2 rewrite Vec.length_to_list.
      split; reflexivity.
    Qed.

    Polymorphic Variable lifta : A -> A * list Exp.t.
    
    Polymorphic Definition lift_A_list (l : list A) : list A * list Exp.t :=
      prod_map_snd (List.concat (A:=Exp.t)) $ shift_pairs $ List.map lifta l.

    Polymorphic Definition lift_A_list_length : forall l,
        length (fst (lift_A_list l)) = length l.
    Proof using.
      intro l; unfold lift_A_list; unravel.
      rewrite fst_prod_map_snd,
        (proj1 (shift_pairs_lengths (map lifta l))),
        map_length.
      reflexivity.
    Qed.
    
    Polymorphic Context {B : Type@{a}}.
    Variable fb : shifter B.
    
    Polymorphic Hypothesis fa_0 : forall c a, fa c 0 a = a.
    Polymorphic Hypothesis fb_0 : forall c b, fb c 0 b = b.

    Local Hint Rewrite shift_exp_0 : core.
    Local Hint Resolve shift_exp_0 : core.
    Local Hint Rewrite PeanoNat.Nat.add_0_r : core.
    Local Hint Rewrite fa_0 : core.
    Local Hint Rewrite fb_0 : core.
    Local Hint Rewrite (@shift_list_0 Exp.t) : core.
    
    Polymorphic Lemma prodn_shift_pairs_single : forall a es,
        prodn_shift_pairs (AS:=[A]%vector) (fa :: []) (a :: []) [es]%vector
        = (a :: [],[es]%vector).
    Proof using A fa fa_0.
      intros; cbn.
      rewrite prodn_shift_pairs_equation_2; unravel.
      rewrite prodn_shift_pairs_equation_1; unravel.
      rewrite ProdN.map_uni2_equation_1.
      autorewrite with core. cbn.
      rewrite shift_list_0 by eauto.
      reflexivity.
    Qed.

    Polymorphic Lemma prodn_shift_pairs_couple :
      forall a b esa esb,
        prodn_shift_pairs
          (AS := [B; A]%vector)
          (fb :: fa :: []) (b :: a :: []) [esb ; esa]%vector
        = (fb (length esb) (length esa) b :: fa 0 (length esb) a :: [],
            [shift_list shift_exp 0 (length esa) esb; esa]%vector).
    Proof using A fa fb fa_0 fb_0.
      intros a b esa esb.
      rewrite prodn_shift_pairs_equation_2. cbn.
      rewrite prodn_shift_pairs_single.
      autorewrite with core. f_equal.
    Qed.

    Polymorphic Definition shift_couple
      (a : A) (b : B) (esa esb : list Exp.t) : A * B * list Exp.t :=
      let '(ba, ess) :=
        prodn_shift_pairs
          (AS := [B; A]%vector)
          (fb :: fa :: [])
          (b :: a :: [])
          [esb ; esa]%vector in
      (ProdN.nth (Fin.FS Fin.F1) ba,
        ProdN.hd ba, Vec.hd ess).

    Polymorphic Lemma shift_couple_length : forall a b esa esb,
        length (snd (shift_couple a b esa esb)) = length esb.
    Proof using.
      intros a b esa esb.
      unfold shift_couple.
      pose proof
        prodn_shift_pairs_inner_length
        (AS := [B; A]%vector)
        (fb :: fa :: [])
        (b :: a :: [])
        [esb ; esa]%vector as h.
      destruct 
        (prodn_shift_pairs
           (AS := [B; A]%vector)
           (fb :: fa :: [])
           (b :: a :: [])
           [esb ; esa]%vector)
        as [ba ess] eqn:hpsp.
      cbn in *.
      apply f_equal with (f:=Vec.hd) in h.
      rewrite vec_hd_map in h.
      assumption.
    Qed.
    
    Polymorphic Lemma shift_couple_spec : forall a b esa esb,
        fst (fst (shift_couple a b esa esb))
        = fa 0 (length esb) a
        /\ snd (fst (shift_couple a b esa esb))
          = fb (length esb) (length esa) b
        /\ snd (shift_couple a b esa esb)
          = shift_list shift_exp 0 (length esa) esb.
    Proof using A fa fb fa_0 fb_0.
      intros a b esa esb.
      destruct (shift_couple a b esa esb) as [[a' b'] esb'] eqn:h.
      unfold shift_couple in h.
      rewrite prodn_shift_pairs_couple in h.
      inv h. unravel. auto.
    Qed.

    Context {C : Type@{a}}.
    Variable fc : shifter C.

    Polymorphic Hypothesis fc_0 : forall ct c, fb ct 0 c = c.
    
    Polymorphic Hypothesis fa_add
      : forall m n a, fa 0 m (fa 0 n a) = fa 0 (m + n) a.

    Local Hint Rewrite fc_0 : core.
    Local Hint Rewrite fa_add : core.
    
    Polymorphic Lemma prodn_shift_pairs_triple :
      forall a b c esa esb esc,
        prodn_shift_pairs
          (AS:=[C; B; A]%vector)
          (fc :: fb :: fa :: [])
          (c :: b :: a :: [])
          [esc; esb; esa]%vector
        = (fc (length esc) (length esb + length esa) c ::
             fb 0 (length esc) (fb (length esb) (length esa) b) ::
             fa 0 (length esc + length esb) a :: [],
            [shift_list shift_exp 0 (length esb + length esa) esc;
             shift_list shift_exp 0 (length esa) esb; esa]%vector).
    Proof using A B C fa fa_0 fa_add fb fb_0 fc.
      intros a b c esa esb esc.
      rewrite prodn_shift_pairs_equation_2. cbn.
      rewrite prodn_shift_pairs_couple.
      rewrite ProdN.map_uni2_equation_2
        with (v := [A]%vector) (f := fb) (fs := fa :: []).
      rewrite ProdN.map_uni2_equation_2  with (v := []%vector) (f := fa) (fs := []).
      rewrite ProdN.map_uni2_equation_1.
      autorewrite with core. reflexivity.
    Qed.

    Polymorphic Definition shift_triple
      (a : A) (b : B) (c : C) (esa esb esc : list Exp.t)
      : A * B * C * list Exp.t * list Exp.t :=
      let '(cba, ess) :=
        prodn_shift_pairs
          (AS:=[C; B; A]%vector)
          (fc :: fb :: fa :: [])
          (c :: b :: a :: [])
          [esc; esb; esa]%vector in
      (ProdN.nth (Fin.FS $ Fin.FS Fin.F1) cba,
        ProdN.nth (Fin.FS Fin.F1) cba,
        ProdN.hd cba, Vec.nth ess (Fin.FS Fin.F1), Vec.hd ess).

    Polymorphic Lemma shift_triple_lengths : forall a b c esa esb esc,
        length (snd (fst (shift_triple a b c esa esb esc))) = length esb
        /\ length (snd (shift_triple a b c esa esb esc)) = length esc.
    Proof using.
      intros a b c esa esb esc.
      unfold shift_triple.
      pose proof prodn_shift_pairs_inner_length
        (AS:=[C; B; A]%vector)
        (fc :: fb :: fa :: [])
        (c :: b :: a :: [])
        [esc; esb; esa]%vector as h.
      destruct (prodn_shift_pairs
                  (AS:=[C; B; A]%vector)
                  (fc :: fb :: fa :: [])
                  (c :: b :: a :: [])
                  [esc; esb; esa]%vector)
        as [cba ess] eqn:hpsp; cbn in *.
      pose proof f_equal Vec.hd h as hhd.
      pose proof f_equal (fun v => Vec.nth v (Fin.FS Fin.F1)) h as hnth.
      cbn in *. rewrite vec_hd_map in hhd.
      rewrite Vec.nth_map with (p2:=Fin.FS Fin.F1) in hnth by reflexivity.
      split; assumption.
    Qed.
    
    Polymorphic Lemma shift_triple_spec :
      forall a b c esa esb esc,
        fst (fst (fst (fst (shift_triple a b c esa esb esc))))
        = fa 0 (length esc + length esb) a
        /\ snd (fst (fst (fst (shift_triple a b c esa esb esc))))
          = fb 0 (length esc) (fb (length esb) (length esa) b)
        /\ snd (fst (fst (shift_triple a b c esa esb esc)))
          = fc (length esc) (length esb + length esa) c
        /\ snd (fst (shift_triple a b c esa esb esc))
          = shift_list shift_exp 0 (length esa) esb
        /\ snd (shift_triple a b c esa esb esc)
          = shift_list shift_exp 0 (length esb + length esa) esc.
    Proof using A B C fa fa_0 fa_add fb fb_0 fc.
      intros a b c esa esb esc.
      destruct (shift_triple a b c esa esb esc) as [[[[a' b'] c'] esb'] esc'] eqn:h.
      unfold shift_triple in h.
      rewrite prodn_shift_pairs_triple in h.
      unravel in *. inv h. auto.
    Qed.
  End ShiftCouple.
End ShiftPairs.

(** [lift_e e = (l, e')],
    where e' is a lifted expression,
    & l is a list of lifted expressions. *)
Fixpoint lift_exp (e : Exp.t) {struct e}
  : Exp.t * list Exp.t :=
  match e with
  | Exp.Bool _
  | Exp.Error _
  | Exp.Var _ _ _ => (e, [])
  | Exp.Bit _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_bit" 0, [e])
  | Exp.VarBit _ _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_varbit" 0, [e])
  | Exp.Int _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_int" 0, [e])
  | Exp.Member t x e
    => let '(e, inits) := lift_exp e in
      (Exp.Member t x e, inits)
  | Exp.Uop t op e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var t "lifted_uop" 0, Exp.Uop t op e :: inits)
  | Exp.Slice hi lo e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var (Typ.Bit (Npos hi - Npos lo + 1)%N) "lifted_slice" 0, Exp.Slice hi lo e :: inits)
  | Exp.Cast t e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var t "lifted_cast" 0, Exp.Cast t e :: inits)
  | Exp.Index t e1 e2 =>
      let '(e1, l1) := lift_exp e1 in
      let '(e2, l2) := lift_exp e2 in
      let '(e1',e2',l2') := shift_couple shift_exp shift_exp e1 e2 l1 l2 in
      (Exp.Index t e1' e2', (l2' ++ l1)%list)
  | Exp.Bop t op e1 e2 => 
      let '(e1, l1) := lift_exp e1 in
      let '(e2, l2) := lift_exp e2 in
      let '(e1',e2',l2') := shift_couple shift_exp shift_exp e1 e2 l1 l2 in
      (Exp.Var t "lifted_bop" 0,
        Exp.Bop t op e1' e2' :: l2' ++ l1)
  | Exp.Lists l es =>
      let '(es', les) := shift_pairs shift_exp $ List.map lift_exp es in
      (Exp.Var (typ_of_lists l es) "lifted_lists" 0, Exp.Lists l es' :: concat les)
  end.

Definition lift_exp_list : list Exp.t -> list Exp.t * list Exp.t :=
  lift_A_list shift_exp lift_exp.

Definition lift_arg (arg : paramarg Exp.t Exp.t)
  : paramarg Exp.t Exp.t * list Exp.t :=
  match arg with
  | PAIn e =>
      let '(e, le) := lift_exp e in (PAIn e, le)
  | PAOut e =>
      let '(e, le) := lift_exp e in (PAOut e, le)
  | PAInOut e =>
      let '(e, le) := lift_exp e in (PAInOut e, le)
  end.

Definition lift_args : Exp.args -> Exp.args * list Exp.t :=
  lift_A_list shift_arg lift_arg.

Definition lift_args_list
  : list Exp.args -> list Exp.args * list Exp.t :=
  lift_A_list (shift_list shift_arg) lift_args.

Fixpoint Unwind (es : list Exp.t) (s : Stm.t) : Stm.t :=
  match es with
  | [] => s
  | e :: es => Unwind es (`let "unwound_var" := inr e `in s)%stm
  end.

Definition lift_trns (e : Trns.t)
  : Trns.t * list Exp.t :=
  match e with
  | Trns.Direct _ => (e,[])
  | Trns.Select e d cases
    => let '(e,le) := lift_exp e in
      (Trns.Select e d cases, le)
  end.

Definition lift_call (fk : Call.t)
  : Call.t * list Exp.t :=
  match fk with
  | Call.Funct _ _ None
  | Call.Method _ _ _ None
  | Call.Inst _ _ => (fk,[])
  | Call.Funct f τs (Some e)
    => let '(e,le) := lift_exp e in (Call.Funct f τs (Some e), le)
  | Call.Method x m τs (Some e)
    => let '(e,le) := lift_exp e in (Call.Method x m τs (Some e), le)
  | Call.Action a es
    => let '(es,les) := lift_exp_list es in (Call.Action a es, les)
  end.

Local Open Scope stm_scope.

Fixpoint lift_stm (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit
  | Stm.Invoke None _
  | Stm.Ret None => s
  | Stm.Ret (Some e)
    => let '(e, le) := lift_exp e in
      Unwind le $ Stm.Ret $ Some e
  | Stm.Trans e =>
      let '(e, le) := lift_trns e in
      Unwind le $ Stm.Trans $ e
  | e1 `:= e2
    => let '(e1, le1) := lift_exp e1 in
      let '(e2, le2) := lift_exp e2 in
      let '(e1', e2', le2') := shift_couple shift_exp shift_exp e1 e2 le1 le2 in
      Unwind (le2' ++ le1) (e1' `:= e2')
  | Stm.Invoke (Some e) t
    => let '(e, le) := lift_exp e in
      Unwind le $ Stm.Invoke (Some e) t
  | Stm.App fk args
    => let '(fk,lfk) := lift_call fk in
      let '(args,largs) := lift_args args in
      let '(args, fk, lfk) := shift_couple (fun c a => map (shift_arg c a)) shift_call args fk largs lfk in
      Unwind (lfk ++ largs) (Stm.App fk args)
  | `let og := inl t `in s => `let og := inl t `in lift_stm s
  | `let og := inr e `in s =>
      let '(e,le) := lift_exp e in
      Unwind le $
        `let og := inr e `in
        shift_stm 1 (length le) $ lift_stm s
  | s₁ `; s₂ => lift_stm s₁ `; lift_stm s₂
  | `if e `then s₁ `else s₂ =>
      let '(e,le) := lift_exp e in
      Unwind
        le $ `if e `then shift_stm 0 (length le) $ lift_stm s₁
        `else shift_stm 0 (length le) $ lift_stm s₂
  end.

Local Close Scope stm_scope.

Definition lift_ctrl (cd : Ctrl.t) : list Ctrl.t * nat :=
  match cd with
  | Ctrl.Var x (inl t) => ([Ctrl.Var x $ inl t], 0)
  | Ctrl.Var x (inr e) =>
      let '(e, es) := lift_exp e in
      ((List.map (Ctrl.Var "" ∘ inr) es ++ [Ctrl.Var x $ inr e])%list, List.length es)
  | Ctrl.Action a cps dps body
    => ([Ctrl.Action a cps dps $ lift_stm body], 0)
  | Ctrl.Table t key acts def =>
      let '(es,mks) := List.split key in
      let '(acts,argss) := List.split acts in
      let '(es,ees) := lift_exp_list es in
      let '(argss,argsss) := lift_args_list argss in
      let '(def,defes) :=
        omap_effect
          []
          (fun '(a,es) => prod_map_fst (pair a) $ lift_exp_list es)
          def in
      let '(def,es,argss,ees,argsss) :=
        shift_triple
          (fun c a => option_map (prod_map_snd (List.map (shift_exp c a))))
          (fun c a => List.map (shift_exp c a))
          (fun c a => List.map (List.map (shift_arg c a)))
          def es argss defes ees argsss in
      ((List.map (Ctrl.Var "" ∘ inr) argsss
          ++ List.map (Ctrl.Var "" ∘ inr) ees
          ++ List.map (Ctrl.Var "" ∘ inr) defes
          ++ [Ctrl.Table
                t
                (List.combine es mks)
                (List.combine acts argss)
                def])%list,
        List.length ees + List.length argsss)
  end.

Fixpoint lift_ctrls (cds : list Ctrl.t) : list Ctrl.t * nat :=
  match cds with
  | [] => ([], 0)
  | d :: ds =>
      let '(d, n) := lift_ctrl d in
      let '(ds, ns) := lift_ctrls ds in
      ((d ++ shift_ctrls 0 n ds)%list, n + ns)
  end.

Definition lift_top (td : Top.t) : Top.t := 
  match td with 
  | Top.Instantiate _ _ _ _ _
  | Top.Extern _ _ _ _ _ => td
  | Top.Control c cparams expr_cparams eps params body apply_blk =>
      let (ds, n) := lift_ctrls body in
      Top.Control
        c cparams expr_cparams eps params ds
        $ shift_stm 0 n $ lift_stm apply_blk  
  | Top.Parser p cparams expr_cparams eps params start states =>
      Top.Parser
        p cparams expr_cparams eps params
        (lift_stm start) $ map lift_stm states
  | Top.Funct f tparams signature body =>
      Top.Funct f tparams signature $ lift_stm body
  end.

Definition lift_program : list Top.t -> list Top.t :=
  map lift_top.
