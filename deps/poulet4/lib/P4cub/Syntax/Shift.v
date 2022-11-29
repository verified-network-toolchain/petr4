From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations
     P4cub.Syntax.IndPrincip.
Import AllCubNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Export Coq.Arith.Compare_dec.

Record shifter : Set :=
  Shifter { cutoff : nat; amt : nat }.

Global Instance eta_shifter : Settable _ :=
  settable! Shifter < cutoff ; amt >.

Section Shift.
  Variable s : shifter.
  
  Definition smother (n : nat) : shifter :=
    s <| cutoff := n + s.(cutoff) |>.

  Definition boost (n : nat) : shifter :=
    s <| amt := n + s.(amt) |>.
  
  Definition shext : shifter :=
    smother 1.
  
  Definition shift_var (x : nat) : nat :=
    if le_lt_dec s.(cutoff) x then s.(amt) + x else x.
  
  Open Scope expr_scope.

  Fixpoint shift_e (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | _ `W _
    | _ `S _
    | Expr.Error _ => e
    | Expr.Var t og x =>
        Expr.Var t og $ shift_var x
    | Expr.Slice hi lo e =>
        Expr.Slice hi lo $ shift_e e
    | Expr.Cast t e =>
        Expr.Cast t $ shift_e e
    | Expr.Uop t u e =>
        Expr.Uop t u $ shift_e e
    | Expr.Bop t o e1 e2 =>
        Expr.Bop t o (shift_e e1) $ shift_e e2
    | Expr.Lists l es =>
        Expr.Lists l $ map shift_e es
    | Expr.Index t e1 e2 =>
        Expr.Index t (shift_e e1) $ shift_e e2
    | Expr.Member t x e =>
        Expr.Member t x $ shift_e e
    end.

  Local Close Scope expr_scope.
  
  Definition shift_arg
    : paramarg Expr.e Expr.e ->
      paramarg Expr.e Expr.e :=
    paramarg_map_same $ shift_e.

  Definition shift_fun_kind
    (fk : Stmt.fun_kind) : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f τs $ option_map shift_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map shift_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m τs $ option_map shift_e oe
    end.

  Definition shift_transition
    (e : Parser.pt) : Parser.pt :=
    match e with
    | Parser.Direct _ => e
    | Parser.Select e d cases
      => Parser.Select (shift_e e) d cases
    end.
End Shift.

Section ShiftList.
  Context {A : Set}.
  Variable f : shifter -> A -> A.
  Variable sh : shifter.

  Fixpoint shift_list (l : list A) : list A :=
    match l with
    | [] => []
    | h :: t => f (smother sh (length t)) h :: shift_list t
    end.
End ShiftList.

Lemma shift_e_add : forall m n e,
    shift_e (Shifter 0 m) (shift_e (Shifter 0 n) e) = shift_e (Shifter 0 (m + n)) e.
Proof.
  intros m n e.
  induction e using custom_e_ind; unravel; f_equal; auto.
  - unfold shift_var; cbn. lia.
  - rewrite map_map.
    apply map_ext_Forall.
    assumption.
Qed.

Section Shift0.
  Variable c : nat.

  Lemma shift_e_0 : forall e, shift_e (Shifter c 0) e = e.
  Proof using.
    intro e.
    induction e using custom_e_ind; unravel;
      f_equal; auto.
    - unfold shift_var.
      destruct_if; reflexivity.
    - apply map_ext_Forall in H.
      rewrite H, map_id; reflexivity.
  Qed.

  Local Hint Rewrite shift_e_0 : core.

  Lemma shift_e_0_map : forall es,
      map (shift_e (Shifter c 0)) es = es.
  Proof using.
    intros es;
      induction es as [| e es ih]; unravel;
      autorewrite with core; f_equal; auto.
  Qed.

  Lemma shift_arg_0 : forall arg, shift_arg (Shifter c 0) arg = arg.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_arg_0 : core.

  Lemma shift_arg_0_map : forall args,
      map (shift_arg (Shifter c 0)) args = args.
  Proof using.
    intros args;
      induction args as [| arg args ih];
      unravel; autorewrite with core;
      f_equal; auto.
  Qed.
  
  Lemma shift_trans_0 : forall p, shift_transition (Shifter c 0) p = p.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.
End Shift0.

Local Open Scope stmt_scope.

Fixpoint shift_s
  (sh : shifter) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Invoke _
  | Stmt.Exit => s
  | Stmt.Return oe
    => Stmt.Return $ option_map (shift_e sh) oe
  | Stmt.Transition e
    => Stmt.Transition $ shift_transition sh e
  | e1 `:= e2 => shift_e sh e1 `:= shift_e sh e2
  | Stmt.Call fk args
    => Stmt.Call fk $ map (shift_arg sh) args
  | Stmt.Apply x eas args
    => Stmt.Apply
        x eas
        $ map (shift_arg sh) args
  | Stmt.Var og te b
    => Stmt.Var
        og (map_sum id (shift_e sh) te)
        $ shift_s (shext sh) b
  | s₁ `; s₂ => shift_s sh s₁ `; shift_s sh s₂
  | If e Then s₁ Else s₂
    => If shift_e sh e Then shift_s sh s₁ Else shift_s sh s₂
  end.

Definition shift_ctrl_decl
  (sh : shifter) (d : Control.d) : Control.d :=
  match d with
  | Control.Var x te => Control.Var x $ map_sum id (shift_e sh) te
  | Control.Action a cps dps s => Control.Action a cps dps $ shift_s sh s
  | Control.Table t key argss =>
      Control.Table
        t (map (fun '(e, mk) => (shift_e sh e, mk)) key)
        (map (fun '(a, args) => (a, map (shift_arg sh) args)) argss)
  end.

Fixpoint shift_ctrl_decls
  (sh : shifter) (ds : list Control.d) : list Control.d :=
  match ds with
  | [] => []
  | Control.Var x te as d :: ds =>
      shift_ctrl_decl sh d :: shift_ctrl_decls (shext sh) ds
  | d :: ds => shift_ctrl_decl sh d :: shift_ctrl_decls sh ds
  end.

(*Definition shift_top_decl
  (sh : shifter) (d : TopDecl.d) : TopDecl.d :=
  match d with
  | TopDecl.Instantiate
  end.*)

Local Close Scope stmt_scope.

Section Shift0.
  Local Hint Rewrite shift_e_0 : core.
  Local Hint Rewrite shift_e_0_map : core.

  Lemma shift_elist_0 : forall es c,
      shift_list shift_e (Shifter c 0) es = es.
  Proof.
    intro es; induction es as [| e es ih];
      intro c; unravel; unfold smother, RecordSet.set; cbn;
      autorewrite with core; f_equal; auto.
  Qed.
  
  Local Hint Rewrite shift_arg_0 : core.
  Local Hint Rewrite shift_arg_0_map : core.
  Local Hint Rewrite shift_trans_0 : core.

  Lemma shift_s_0 : forall s c, shift_s (Shifter c 0) s = s.
  Proof using.
    intro s;
      induction s;
      intro c; unravel;
      autorewrite with core;
      unfold shext, smother, RecordSet.set; unravel;
      f_equal; auto.
    - destruct e; unravel;
        autorewrite with core; reflexivity.
    - destruct expr; unravel;
        autorewrite with core; reflexivity.
  Qed.
End Shift0.

(** Philip Wadler style de Bruijn shifts for expression variables. *)

Section Rename.
  Variable ρ : nat -> nat.

  Definition ext (x : nat) : nat :=
    match x with
    | O   => O
    | S n => S $ ρ x
    end.

  (*Definition add_to_name (n : nat) : nat :=*)
    

  Local Open Scope expr_scope.
  
  Fixpoint rename_e  (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | _ `W _
    | _ `S _
    | Expr.Error _     => e
    | Expr.Var t og x     => Expr.Var t og $ ρ x
    | Expr.Slice h l e => Expr.Slice h l $ rename_e e
    | Expr.Cast t e    => Expr.Cast t $ rename_e e
    | Expr.Uop t op e  => Expr.Uop t op $ rename_e e
    | Expr.Index t e1 e2
      => Expr.Index t (rename_e e1) $ rename_e e2
    | Expr.Member t x e
      => Expr.Member t x $ rename_e e
    | Expr.Bop t op e1 e2
      => Expr.Bop t op (rename_e e1) $ rename_e e2
    | Expr.Lists l es => Expr.Lists l $ map rename_e es
    end.
  
  Local Close Scope expr_scope.

  Definition rename_arg
    : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
    paramarg_map_same $ rename_e.

  Definition rename_fun_kind (fk : Stmt.fun_kind)
    : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f τs $ option_map rename_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map rename_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m τs $ option_map rename_e oe
    end.

  Definition rename_transition (e : Parser.pt) : Parser.pt :=
    match e with
    | Parser.Direct _ => e
    | Parser.Select e d cases
      => Parser.Select (rename_e e) d cases
    end.
End Rename.

Local Open Scope stmt_scope.

Fixpoint rename_s (ρ : nat -> nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Invoke _
  | Stmt.Exit => s
  | Stmt.Return oe
    => Stmt.Return $ option_map (rename_e ρ) oe
  | Stmt.Transition e
    => Stmt.Transition $ rename_transition ρ e
  | e1 `:= e2 => rename_e ρ e1 `:= rename_e ρ e2
  | Stmt.Call fk args
    => Stmt.Call fk $ map (rename_arg ρ) args
  | Stmt.Apply x eas args
    => Stmt.Apply
        x eas
        $ map (rename_arg ρ) args
  | Stmt.Var og te b
    => Stmt.Var
        og (map_sum id (rename_e ρ) te)
        $ rename_s (ext ρ) b
  | s₁ `; s₂ => rename_s ρ s₁ `; rename_s ρ s₂
  | If e Then s₁ Else s₂
    => If rename_e ρ e Then rename_s ρ s₁ Else rename_s ρ s₂
  end.

Local Close Scope stmt_scope.

Section TermSub.
  Variable σ : nat -> Expr.t -> String.string -> Expr.e.

  Local Open Scope expr_scope.
  
  Definition exts (x : nat) (t : Expr.t) (original_name : String.string) : Expr.e :=
    match x with
    | O => Expr.Var t original_name O
    | S n => rename_e S $ σ n t original_name
    end.

  Fixpoint esub_e (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | _ `W _
    | _ `S _
    | Expr.Error _ => e
    | Expr.Var t og x => σ x t og
    | Expr.Slice hi lo e => Expr.Slice hi lo $ esub_e e
    | Expr.Cast t e => Expr.Cast t $ esub_e e
    | Expr.Uop t op e => Expr.Uop t op $ esub_e e
    | Expr.Bop t op e₁ e₂ => Expr.Bop t op (esub_e e₁) $ esub_e e₂
    | Expr.Lists ls es => Expr.Lists ls $ map esub_e es
    | Expr.Index t e₁ e₂ => Expr.Index t (esub_e e₁) $ esub_e e₂
    | Expr.Member t x e => Expr.Member t x $ esub_e e
    end.
  
  Local Close Scope expr_scope.

  Definition esub_arg
    : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
    paramarg_map_same $ esub_e.

  Definition esub_transition (pe : Parser.pt) : Parser.pt :=
    match pe with
    | Parser.Direct s => Parser.Direct s
    | Parser.Select discriminee default cases =>
        Parser.Select (esub_e discriminee) default cases
    end.

  Definition esub_fun_kind (fk : Stmt.fun_kind) : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f τs $ option_map esub_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map esub_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m τs $ option_map esub_e oe
    end.
End TermSub.

Local Open Scope stmt.

Fixpoint esub_s (σ : nat -> Expr.t -> String.string -> Expr.e) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Return None
  | Stmt.Invoke _
  | Stmt.Exit => s
  | Stmt.Return (Some e) => Stmt.Return $ Some $ esub_e σ e
  | Stmt.Transition e => Stmt.Transition $ esub_transition σ e
  | e₁ `:= e₂ => esub_e σ e₁ `:= esub_e σ e₂
  | Stmt.Call fk args => Stmt.Call (esub_fun_kind σ fk) $ List.map (esub_arg σ) args
  | Stmt.Apply inst eargs args => Stmt.Apply inst eargs $ map (esub_arg σ) args
  | Stmt.Var og te s => Stmt.Var og (map_sum id (esub_e σ) te) $ esub_s (exts σ) s
  | s₁ `; s₂ => esub_s σ s₁ `; esub_s σ s₂
  | If e Then s₁ Else s₂ => If esub_e σ e Then esub_s σ s₁ Else esub_s σ s₂
  end.

Local Close Scope stmt.
