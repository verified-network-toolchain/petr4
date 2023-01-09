Require Import Coq.Strings.String Coq.NArith.BinNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     Utils.ForallMap.
Import ListNotations AllCubNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

Section ShiftPairs.
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.
  Polymorphic Variable f : shifter -> A -> A.

  Polymorphic Fixpoint shift_pairs (l : list (A * list Expr.e)) : list (A * list Expr.e) :=
    match l with
    | [] => []
    | (a, es) :: l
      => let n := list_sum $ map (@length _) $ map snd l in
        (f (Shifter (length es) n) a,
          shift_list shift_e (Shifter 0 n) es) ::
          map (fun '(a, es') => (f (Shifter 0 $ length es) a, es')) (shift_pairs l)
    end.
  
  Polymorphic Lemma shift_pairs_length : forall l,
      length (shift_pairs l) = length l.
  Proof using.
    intro l; induction l as [| [a es] l ih];
      unravel; f_equal; auto.
    rewrite map_length. assumption.                     
  Qed.

  Polymorphic Lemma shift_pairs_inner_length : forall l,
      map (length (A:=Expr.e)) (map snd (shift_pairs l))
      = map (length (A:=Expr.e)) (map snd l).
  Proof using.
    intro l; induction l as [| [a es] l ih];
      unravel; f_equal; auto.
    - rewrite shift_list_length.
      reflexivity.
    - rewrite map_snd_map,map_id.
      assumption.
  Qed.
End ShiftPairs.

(** [lift_e e = (l, e')],
    where e' is a lifted expression,
    & l is a list of lifted expressions. *)
Fixpoint lift_e (e : Expr.e) {struct e}
  : Expr.e * list Expr.e :=
  match e with
  | Expr.Bool _
  | Expr.Error _
  | Expr.Var _ _ _ => (e, [])
  | Expr.Bit _ _ =>
      (Expr.Var (t_of_e e) "lifted_bit" 0, [e])
  | Expr.VarBit _ _ _ =>
      (Expr.Var (t_of_e e) "lifted_varbit" 0, [e])
  | Expr.Int _ _ =>
      (Expr.Var (t_of_e e) "lifted_int" 0, [e])
  | Expr.Member t x e
    => let '(e, inits) := lift_e e in
      (Expr.Member t x e, inits)
  | Expr.Uop t op e =>
      let '(e, inits) := lift_e e in
      (Expr.Var t "lifted_uop" 0, Expr.Uop t op e :: inits)
  | Expr.Slice hi lo e =>
      let '(e, inits) := lift_e e in
      (Expr.Var (Expr.TBit (Npos hi - Npos lo + 1)%N) "lifted_slice" 0, Expr.Slice hi lo e :: inits)
  | Expr.Cast t e =>
      let '(e, inits) := lift_e e in
      (Expr.Var t "lifted_cast" 0, Expr.Cast t e :: inits)
  | Expr.Index t e1 e2 =>
      let '(e1, l1) := lift_e e1 in
      let '(e2, l2) := lift_e e2 in
      (Expr.Index
         t
         (shift_e (Shifter 0 (length l2)) e1)
         (shift_e (Shifter (length l2) (length l1)) e2),
        shift_list shift_e (Shifter 0 (length l1)) l2 ++ l1)
  | Expr.Bop t op e1 e2 => 
      let '(e1, l1) := lift_e e1 in
      let '(e2, l2) := lift_e e2 in
      (Expr.Var t "lifted_bop" 0,
        Expr.Bop
          t op
          (shift_e (Shifter 0 (length l2)) e1)
          (shift_e (Shifter (length l2) (length l1)) e2)
          :: shift_list shift_e (Shifter 0 (length l1)) l2 ++ l1)
  | Expr.Lists l es =>
      let '(es', les) := List.split (shift_pairs shift_e $ List.map lift_e es) in
      (Expr.Var (t_of_lists l es) "lifted_lists" 0, Expr.Lists l es' :: concat les)
  end.

Definition lift_e_list (es : list Expr.e) : list Expr.e * list Expr.e :=
  let '(es, les) := List.split (shift_pairs shift_e $ List.map lift_e es) in
  (es, concat les).

Definition lift_arg (arg : paramarg Expr.e Expr.e)
  : paramarg Expr.e Expr.e * list Expr.e :=
  match arg with
  | PAIn e =>
      let '(e, le) := lift_e e in (PAIn e, le)
  | PAOut e =>
      let '(e, le) := lift_e e in (PAOut e, le)
  | PAInOut e =>
      let '(e, le) := lift_e e in (PAInOut e, le)
  end.

Definition lift_args (args : Expr.args) : Expr.args * list Expr.e :=
  let '(args, les) := List.split (shift_pairs shift_arg $ List.map lift_arg args) in
  (args, concat les).

Definition lift_args_list
  (argss : list Expr.args) : list Expr.args * list Expr.e :=
  let '(argss, argsss) :=
    List.split (shift_pairs (shift_list shift_arg) $ map lift_args argss) in
  (argss, concat argsss).

Fixpoint Unwind (es : list Expr.e) (s : Stmt.s) : Stmt.s :=
  match es with
  | [] => s
  | e :: es => Unwind es (Stmt.Var "unwound_var" (inr e) s)
  end.

Definition lift_trans (e : Parser.trns)
  : Parser.trns * list Expr.e :=
  match e with
  | Parser.Direct _ => (e,[])
  | Parser.Select e d cases
    => let '(e,le) := lift_e e in
      (Parser.Select e d cases, le)
  end.

Definition lift_fun_kind (fk : Stmt.fun_kind)
  : Stmt.fun_kind * list Expr.e  :=
  match fk with
  | Stmt.Funct _ _ None
  | Stmt.Method _ _ _ None => (fk,[])
  | Stmt.Funct f τs (Some e)
    => let '(e,le) := lift_e e in (Stmt.Funct f τs (Some e), le)
  | Stmt.Method x m τs (Some e)
    => let '(e,le) := lift_e e in (Stmt.Method x m τs (Some e), le)
  | Stmt.Action a es
    => let '(es,les) := lift_e_list es in (Stmt.Action a es, les)
  end.

Local Open Scope stmt_scope.

Fixpoint lift_s (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Invoke _
  | Stmt.Exit
  | Stmt.Return None => s
  | Stmt.Return (Some e)
    => let '(e, le) := lift_e e in
      Unwind le $ Stmt.Return $ Some e
  | Stmt.Transition e =>
      let '(e, le) := lift_trans e in
      Unwind le $ Stmt.Transition $ e
  | e1 `:= e2
    => let '(e1, le1) := lift_e e1 in
      let '(e2, le2) := lift_e e2 in
      Unwind
        (shift_list shift_e (Shifter 0 (length le1)) le2 ++ le1)
        (shift_e (Shifter 0 (length le2)) e1
           `:= shift_e (Shifter (length le2) (length le1)) e2)
  | Stmt.Call fk args
    => let '(fk,lfk) := lift_fun_kind fk in
      let '(args,largs) := lift_args args in
      Unwind
        (shift_list shift_e (Shifter 0 (length largs)) lfk ++ largs)
        (Stmt.Call
           (shift_fun_kind (Shifter (length lfk) (length largs)) fk)
           (map (shift_arg $ Shifter 0 (length lfk)) args))
  | Stmt.Apply x exts args
    => let '(args, inits) := lift_args args in
      Unwind
        inits
        (Stmt.Apply x exts args)
  | Stmt.Var og (inl t) s => Stmt.Var og (inl t) $ lift_s s
  | Stmt.Var og (inr e) s =>
      let '(e,le) := lift_e e in
      Unwind
        le $ Stmt.Var og (inr e)
        $ shift_s (Shifter 1 (length le)) $ lift_s s
  | s₁ `; s₂ => lift_s s₁ `; lift_s s₂
  | If e Then s₁ Else s₂ =>
      let '(e,le) := lift_e e in
      Unwind
        le $ If e Then shift_s (Shifter 0 (length le)) $ lift_s s₁
        Else shift_s (Shifter 0 (length le)) $ lift_s s₂
  end.

Local Close Scope stmt_scope.

Definition lift_control_decl (cd : Control.d) : list Control.d * nat :=
  match cd with
  | Control.Var x (inl t) => ([Control.Var x $ inl t], 0)
  | Control.Var x (inr e) =>
      let '(e, es) := lift_e e in
      (List.map (Control.Var "" ∘ inr) es ++ [Control.Var x $ inr e], List.length es)
  | Control.Action a cps dps body
    => ([Control.Action a cps dps $ lift_s body], 0)
  | Control.Table t key acts =>
      let '(es,mks) := List.split key in
      let '(acts,argss) := List.split acts in
      let '(es,ees) := lift_e_list es in
      let '(argss,argsss) := lift_args_list argss in
      (List.map (Control.Var "" ∘ inr) argsss
         ++ List.map (Control.Var "" ∘ inr)
         (List.map (shift_e (Shifter 0 $ length argsss)) ees)
         ++ [Control.Table
               t
               (List.combine (map (shift_e $ Shifter (length ees) $ length argsss) es) mks)
               (List.combine acts $ map (shift_list shift_arg $ Shifter 0 $ length ees) argss)],
        List.length ees + List.length argsss)
  end.

Fixpoint lift_control_decls (cds : list Control.d) : list Control.d * nat :=
  match cds with
  | [] => ([], 0)
  | d :: ds =>
      let '(d, n) := lift_control_decl d in
      let '(ds, ns) := lift_control_decls ds in
      (d ++ shift_ctrl_decls (Shifter 0 n) ds, n + ns)
  end.

Definition lift_top_decl (td : TopDecl.d) : TopDecl.d := 
  match td with 
  | TopDecl.Instantiate _ _ _ _ _
  | TopDecl.Extern _ _ _ _ _ => td
  | TopDecl.Control c cparams expr_cparams eps params body apply_blk =>
      let (ds, n) := lift_control_decls body in
      TopDecl.Control
        c cparams expr_cparams eps params ds
        $ shift_s (Shifter 0 n) $ lift_s apply_blk  
  | TopDecl.Parser p cparams expr_cparams eps params start states =>
      TopDecl.Parser
        p cparams expr_cparams eps params
        (lift_s start) $ map lift_s states
  | TopDecl.Funct f tparams signature body =>
      TopDecl.Funct f tparams signature $ lift_s body
  end.

Definition lift_program : list TopDecl.d -> list TopDecl.d :=
  map lift_top_decl.
