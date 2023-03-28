Require Import Coq.Strings.String Coq.NArith.BinNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     Utils.ForallMap
     Utils.VecUtil.
Import ListNotations.
From Equations Require Import Equations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

Section ShiftPairs.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.
  Polymorphic Variable f : shifter -> A -> A.

  Polymorphic Equations shift_pairs :
    forall {n : nat}, Vec.t (A * list Exp.t) n -> Vec.t (A * list Exp.t) n := {
      shift_pairs [] := [];
      shift_pairs ((a, es) :: v) :=
        let m := vec_sum $ Vec.map (length (A:=Exp.t)) $ Vec.map snd v in
        (f (Shifter (length es) m) a,
          shift_list shift_exp (Shifter 0 m) es) ::
          Vec.map (fun '(a, es') => (f (Shifter 0 $ length es) a, es')) (shift_pairs v) }.

  Polymorphic Lemma shift_pairs_inner_length : forall {n} (v : Vec.t _ n),
      Vec.map (length (A:=Exp.t)) (Vec.map snd (shift_pairs v))
      = Vec.map (length (A:=Exp.t)) (Vec.map snd v).
  Proof using.
    intros n v.
    depind v; unravel.
    - rewrite shift_pairs_equation_1. reflexivity.
    - destruct h as [a es].
      rewrite shift_pairs_equation_2. unravel.
      rewrite vec_ignore_map_snd_map, shift_list_length.
      f_equal. assumption.
  Qed.
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
      (Exp.Index
         t
         (shift_exp (Shifter 0 (length l2)) e1)
         (shift_exp (Shifter (length l2) (length l1)) e2),
        shift_list shift_exp (Shifter 0 (length l1)) l2 ++ l1)
  | Exp.Bop t op e1 e2 => 
      let '(e1, l1) := lift_exp e1 in
      let '(e2, l2) := lift_exp e2 in
      (Exp.Var t "lifted_bop" 0,
        Exp.Bop
          t op
          (shift_exp (Shifter 0 (length l2)) e1)
          (shift_exp (Shifter (length l2) (length l1)) e2)
          :: shift_list shift_exp (Shifter 0 (length l1)) l2 ++ l1)
  | Exp.Lists l es =>
      let '(es', les) := List.split (shift_pairs shift_exp $ List.map lift_exp es) in
      (Exp.Var (typ_of_lists l es) "lifted_lists" 0, Exp.Lists l es' :: concat les)
  end.

Definition lift_exp_list (es : list Exp.t) : list Exp.t * list Exp.t :=
  let '(es, les) := List.split (shift_pairs shift_exp $ List.map lift_exp es) in
  (es, concat les).

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

Definition lift_args (args : Exp.args) : Exp.args * list Exp.t :=
  let '(args, les) := List.split (shift_pairs shift_arg $ List.map lift_arg args) in
  (args, concat les).

Definition lift_args_list
  (argss : list Exp.args) : list Exp.args * list Exp.t :=
  let '(argss, argsss) :=
    List.split (shift_pairs (shift_list shift_arg) $ map lift_args argss) in
  (argss, concat argsss).

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
      Unwind
        (shift_list shift_exp (Shifter 0 (length le1)) le2 ++ le1)
        (shift_exp (Shifter 0 (length le2)) e1
           `:= shift_exp (Shifter (length le2) (length le1)) e2)
  | Stm.Invoke (Some e) t
    => let '(e, le) := lift_exp e in
      Unwind le $ Stm.Invoke (Some e) t
  | Stm.App fk args
    => let '(fk,lfk) := lift_call fk in
      let '(args,largs) := lift_args args in
      Unwind
        (shift_list shift_exp (Shifter 0 (length largs)) lfk ++ largs)
        (Stm.App
           (shift_call (Shifter (length lfk) (length largs)) fk)
           (map (shift_arg $ Shifter 0 (length lfk)) args))
  | `let og := inl t `in s => `let og := inl t `in lift_stm s
  | `let og := inr e `in s =>
      let '(e,le) := lift_exp e in
      Unwind le $
        `let og := inr e `in
        shift_stm (Shifter 1 (length le)) $ lift_stm s
  | s₁ `; s₂ => lift_stm s₁ `; lift_stm s₂
  | `if e `then s₁ `else s₂ =>
      let '(e,le) := lift_exp e in
      Unwind
        le $ `if e `then shift_stm (Shifter 0 (length le)) $ lift_stm s₁
        `else shift_stm (Shifter 0 (length le)) $ lift_stm s₂
  end.

Local Close Scope stm_scope.

Definition lift_ctrl (cd : Ctrl.t) : list Ctrl.t * nat :=
  match cd with
  | Ctrl.Var x (inl t) => ([Ctrl.Var x $ inl t], 0)
  | Ctrl.Var x (inr e) =>
      let '(e, es) := lift_exp e in
      (List.map (Ctrl.Var "" ∘ inr) es ++ [Ctrl.Var x $ inr e], List.length es)
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
          (fun '(a,es) => map_fst (pair a) $ lift_exp_list es)
          def in
      (List.map (Ctrl.Var "" ∘ inr) argsss
         ++ List.map (Ctrl.Var "" ∘ inr)
         (List.map (shift_exp (Shifter 0 $ length argsss)) ees)
         ++ List.map (Ctrl.Var "" ∘ inr)
         (List.map (shift_exp (Shifter 0 (length es + length argsss))) defes)
         ++ [Ctrl.Table
               t
               (List.combine
                  (map (shift_exp $ Shifter 0 $ length defes)
                     $ map (shift_exp $ Shifter (length ees) $ length argsss) es) mks)
               (List.combine acts
                  $ map
                  (shift_list shift_arg
                     $ Shifter 0 (length defes + length ees)) argss)
                  (option_map
                     (fun '(a, es) =>
                        (a, map (shift_exp $ Shifter (length defes) (length ees + length argss)) es))
                     def)],
        List.length ees + List.length argsss)
  end.

Fixpoint lift_ctrls (cds : list Ctrl.t) : list Ctrl.t * nat :=
  match cds with
  | [] => ([], 0)
  | d :: ds =>
      let '(d, n) := lift_ctrl d in
      let '(ds, ns) := lift_ctrls ds in
      (d ++ shift_ctrls (Shifter 0 n) ds, n + ns)
  end.

Definition lift_top (td : Top.t) : Top.t := 
  match td with 
  | Top.Instantiate _ _ _ _ _
  | Top.Extern _ _ _ _ _ => td
  | Top.Control c cparams expr_cparams eps params body apply_blk =>
      let (ds, n) := lift_ctrls body in
      Top.Control
        c cparams expr_cparams eps params ds
        $ shift_stm (Shifter 0 n) $ lift_stm apply_blk  
  | Top.Parser p cparams expr_cparams eps params start states =>
      Top.Parser
        p cparams expr_cparams eps params
        (lift_stm start) $ map lift_stm states
  | Top.Funct f tparams signature body =>
      Top.Funct f tparams signature $ lift_stm body
  end.

Definition lift_program : list Top.t -> list Top.t :=
  map lift_top.
