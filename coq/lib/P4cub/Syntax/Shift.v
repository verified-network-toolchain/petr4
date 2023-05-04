From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations
     P4cub.Syntax.IndPrincip.
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
  
  Open Scope exp_scope.
  
  Fixpoint shift_exp (e : Exp.t) : Exp.t :=
    match e with
    | Exp.Bool _
    | _ `W _
    | _ `S _
    | Exp.VarBit _ _ _
    | Exp.Error _ => e
    | Exp.Var t og x =>
        Exp.Var t og $ shift_var x
    | Exp.Slice hi lo e =>
        Exp.Slice hi lo $ shift_exp e
    | Exp.Cast t e =>
        Exp.Cast t $ shift_exp e
    | Exp.Uop t u e =>
        Exp.Uop t u $ shift_exp e
    | Exp.Bop t o e1 e2 =>
        Exp.Bop t o (shift_exp e1) $ shift_exp e2
    | Exp.Lists l es =>
        Exp.Lists l $ map shift_exp es
    | Exp.Index t e1 e2 =>
        Exp.Index t (shift_exp e1) $ shift_exp e2
    | Exp.Member t x e =>
        Exp.Member t x $ shift_exp e
    end.

  Local Close Scope exp_scope.
  
  Definition shift_arg
    : paramarg Exp.t Exp.t ->
      paramarg Exp.t Exp.t :=
    paramarg_map_same $ shift_exp.

  Definition shift_call
    (fk : Call.t) : Call.t :=
    match fk with
    | Call.Funct f τs oe
      => Call.Funct f τs $ option_map shift_exp oe
    | Call.Action a cargs
      => Call.Action a $ map shift_exp cargs
    | Call.Method e m τs oe
      => Call.Method e m τs $ option_map shift_exp oe
    | Call.Inst _ _ => fk
    end.

  Definition shift_trns
    (e : Trns.t) : Trns.t :=
    match e with
    | Trns.Direct _ => e
    | Trns.Select e d cases
      => Trns.Select (shift_exp e) d cases
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

  Lemma shift_list_length : forall l,
      length (shift_list l) = length l.
  Proof using.
    intro l; induction l as [| h t ih];
      cbn; f_equal; auto.
  Qed.
End ShiftList.

Lemma shift_exp_add : forall m n e,
    shift_exp (Shifter 0 m) (shift_exp (Shifter 0 n) e) = shift_exp (Shifter 0 (m + n)) e.
Proof.
  intros m n e.
  induction e using custom_exp_ind; unravel; f_equal; auto.
  - unfold shift_var; cbn. lia.
  - rewrite map_map.
    apply map_ext_Forall.
    assumption.
Qed.

Section Shift0.
  Variable c : nat.

  Lemma shift_exp_0 : forall e, shift_exp (Shifter c 0) e = e.
  Proof using.
    intro e.
    induction e using custom_exp_ind; unravel;
      f_equal; auto.
    - unfold shift_var.
      destruct_if; reflexivity.
    - apply map_ext_Forall in H.
      rewrite H, map_id; reflexivity.
  Qed.

  Local Hint Rewrite shift_exp_0 : core.

  Lemma shift_exp_0_map : forall es,
      map (shift_exp (Shifter c 0)) es = es.
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
  
  Lemma shift_trans_0 : forall p, shift_trns (Shifter c 0) p = p.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.
End Shift0.

Local Open Scope stm_scope.

Fixpoint shift_stm
  (sh : shifter) (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit => s
  | Stm.Ret oe
    => Stm.Ret $ option_map (shift_exp sh) oe
  | Stm.Trans e
    => Stm.Trans $ shift_trns sh e
  | e1 `:= e2 => shift_exp sh e1 `:= shift_exp sh e2
  | Stm.SetValidity b e => Stm.SetValidity b $ shift_exp sh e
  | Stm.Invoke e t
    => Stm.Invoke (option_map (shift_exp sh) e) t
  | Stm.App fk args
    => Stm.App (shift_call sh fk) $ map (shift_arg sh) args
  |`let og := te `in b
    => `let og := map_sum id (shift_exp sh) te `in shift_stm (shext sh) b
  | s₁ `; s₂ => shift_stm sh s₁ `; shift_stm sh s₂
  | `if e `then s₁ `else s₂
    => `if shift_exp sh e `then shift_stm sh s₁ `else shift_stm sh s₂
  end.

Definition shift_ctrl
  (sh : shifter) (d : Ctrl.t) : Ctrl.t :=
  match d with
  | Ctrl.Var x te => Ctrl.Var x $ map_sum id (shift_exp sh) te
  | Ctrl.Action a cps dps s => Ctrl.Action a cps dps $ shift_stm sh s
  | Ctrl.Table t key argss def =>
      Ctrl.Table
        t (map (fun '(e, mk) => (shift_exp sh e, mk)) key)
        (map (fun '(a, args) => (a, map (shift_arg sh) args)) argss)
        $ option_map (fun '(a, es) => (a, map (shift_exp sh) es)) def
  end.

Fixpoint shift_ctrls
  (sh : shifter) (ds : list Ctrl.t) : list Ctrl.t :=
  match ds with
  | [] => []
  | Ctrl.Var x te as d :: ds =>
      shift_ctrl sh d :: shift_ctrls (shext sh) ds
  | d :: ds => shift_ctrl sh d :: shift_ctrls sh ds
  end.

(*Definition shift_top_decl
  (sh : shifter) (d : TopDecl.d) : TopDecl.d :=
  match d with
  | TopDecl.Instantiate
  end.*)

Local Close Scope stm_scope.

Section Shift0.
  Local Hint Rewrite shift_exp_0 : core.
  Local Hint Rewrite shift_exp_0_map : core.

  Lemma shift_explist_0 : forall es c,
      shift_list shift_exp (Shifter c 0) es = es.
  Proof.
    intro es; induction es as [| e es ih];
      intro c; unravel; unfold smother, RecordSet.set; cbn;
      autorewrite with core; f_equal; auto.
  Qed.
  
  Local Hint Rewrite shift_arg_0 : core.
  Local Hint Rewrite shift_arg_0_map : core.
  Local Hint Rewrite shift_trans_0 : core.

  Lemma shift_call_0 : forall fk c,
      shift_call (Shifter c 0) fk = fk.
  Proof using.
    intros [f ts [e |] | a es | ext mthd ts [e |] | ? ?] c; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_call_0 : core.
  
  Lemma shift_stm_0 : forall s c, shift_stm (Shifter c 0) s = s.
  Proof using.
    intro s;
      induction s;
      intro c; unravel;
      autorewrite with core;
      unfold shext, smother, RecordSet.set; unravel;
      f_equal; auto.
    - destruct e; unravel;
        autorewrite with core; reflexivity.
    - destruct lhs; unravel;
        autorewrite with core; reflexivity.
    - destruct init; unravel;
        autorewrite with core; reflexivity.
  Qed.
End Shift0.

(** Philip Wadler style de Bruijn shifts for expession variables. *)

Section Rename.
  Variable ρ : nat -> nat.

  Definition ext (x : nat) : nat :=
    match x with
    | O   => O
    | S n => S $ ρ x
    end.

  (*Definition add_to_name (n : nat) : nat :=*)
    

  Local Open Scope exp_scope.
  
  Fixpoint rename_exp  (e : Exp.t) : Exp.t :=
    match e with
    | Exp.Bool _
    | _ `W _
    | _ `S _
    | Exp.VarBit _ _ _
    | Exp.Error _     => e
    | Exp.Var t og x  => Exp.Var t og $ ρ x
    | Exp.Slice h l e => Exp.Slice h l $ rename_exp e
    | Exp.Cast t e    => Exp.Cast t $ rename_exp e
    | Exp.Uop t op e  => Exp.Uop t op $ rename_exp e
    | Exp.Index t e1 e2
      => Exp.Index t (rename_exp e1) $ rename_exp e2
    | Exp.Member t x e
      => Exp.Member t x $ rename_exp e
    | Exp.Bop t op e1 e2
      => Exp.Bop t op (rename_exp e1) $ rename_exp e2
    | Exp.Lists l es => Exp.Lists l $ map rename_exp es
    end.
  
  Local Close Scope exp_scope.

  Definition rename_arg
    : paramarg Exp.t Exp.t -> paramarg Exp.t Exp.t :=
    paramarg_map_same $ rename_exp.

  Definition rename_call (fk : Call.t)
    : Call.t :=
    match fk with
    | Call.Funct f τs oe
      => Call.Funct f τs $ option_map rename_exp oe
    | Call.Action a cargs
      => Call.Action a $ map rename_exp cargs
    | Call.Method e m τs oe
      => Call.Method e m τs $ option_map rename_exp oe
    | Call.Inst _ _ => fk
    end.

  Definition rename_trns (e : Trns.t) : Trns.t :=
    match e with
    | Trns.Direct _ => e
    | Trns.Select e d cases
      => Trns.Select (rename_exp e) d cases
    end.
End Rename.

Local Open Scope stm_scope.

Fixpoint rename_stm (ρ : nat -> nat) (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit => s
  | Stm.Ret oe
    => Stm.Ret $ option_map (rename_exp ρ) oe
  | Stm.Trans e
    => Stm.Trans $ rename_trns ρ e
  | e1 `:= e2 => rename_exp ρ e1 `:= rename_exp ρ e2
  | Stm.SetValidity b e => Stm.SetValidity b $ rename_exp ρ e
  | Stm.Invoke e t
    => Stm.Invoke (option_map (rename_exp ρ) e) t
  | Stm.App fk args
    => Stm.App fk $ map (rename_arg ρ) args
  | `let og := te `in b
    => `let og := map_sum id (rename_exp ρ) te `in rename_stm (ext ρ) b
  | s₁ `; s₂ => rename_stm ρ s₁ `; rename_stm ρ s₂
  | `if e `then s₁ `else s₂
    => `if rename_exp ρ e `then rename_stm ρ s₁ `else rename_stm ρ s₂
  end.

Local Close Scope stm_scope.

Section TermSub.
  Variable σ : nat -> Typ.t -> String.string -> Exp.t.

  Local Open Scope exp_scope.
  
  Definition exts (x : nat) (t : Typ.t) (original_name : String.string) : Exp.t :=
    match x with
    | O => Exp.Var t original_name O
    | S n => rename_exp S $ σ n t original_name
    end.

  Fixpoint exp_sub_exp (e : Exp.t) : Exp.t :=
    match e with
    | Exp.Bool _
    | _ `W _
    | _ `S _
    | Exp.VarBit _ _ _
    | Exp.Error _ => e
    | Exp.Var t og x => σ x t og
    | Exp.Slice hi lo e => Exp.Slice hi lo $ exp_sub_exp e
    | Exp.Cast t e => Exp.Cast t $ exp_sub_exp e
    | Exp.Uop t op e => Exp.Uop t op $ exp_sub_exp e
    | Exp.Bop t op e₁ e₂ => Exp.Bop t op (exp_sub_exp e₁) $ exp_sub_exp e₂
    | Exp.Lists ls es => Exp.Lists ls $ map exp_sub_exp es
    | Exp.Index t e₁ e₂ => Exp.Index t (exp_sub_exp e₁) $ exp_sub_exp e₂
    | Exp.Member t x e => Exp.Member t x $ exp_sub_exp e
    end.
  
  Local Close Scope exp_scope.

  Definition exp_sub_arg
    : paramarg Exp.t Exp.t -> paramarg Exp.t Exp.t :=
    paramarg_map_same $ exp_sub_exp.

  Definition exp_sub_trns (pe : Trns.t) : Trns.t :=
    match pe with
    | Trns.Direct s => Trns.Direct s
    | Trns.Select discriminee default cases =>
        Trns.Select (exp_sub_exp discriminee) default cases
    end.

  Definition exp_sub_call (fk : Call.t) : Call.t :=
    match fk with
    | Call.Funct f τs oe
      => Call.Funct f τs $ option_map exp_sub_exp oe
    | Call.Action a cargs
      => Call.Action a $ map exp_sub_exp cargs
    | Call.Method e m τs oe
      => Call.Method e m τs $ option_map exp_sub_exp oe
    | Call.Inst _ _ => fk
    end.
End TermSub.

Local Open Scope stm.

Fixpoint exp_sub_stm (σ : nat -> Typ.t -> String.string -> Exp.t) (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Ret None
  | Stm.Exit => s
  | Stm.Ret (Some e) => Stm.Ret $ Some $ exp_sub_exp σ e
  | Stm.Trans e => Stm.Trans $ exp_sub_trns σ e
  | e₁ `:= e₂ => exp_sub_exp σ e₁ `:= exp_sub_exp σ e₂
  | Stm.SetValidity b e => Stm.SetValidity b $ exp_sub_exp σ e
  | Stm.Invoke e t => Stm.Invoke (option_map (exp_sub_exp σ) e) t
  | Stm.App fk args => Stm.App (exp_sub_call σ fk) $ List.map (exp_sub_arg σ) args
  | `let og := te `in s => `let og := map_sum id (exp_sub_exp σ) te `in exp_sub_stm (exts σ) s
  | s₁ `; s₂ => exp_sub_stm σ s₁ `; exp_sub_stm σ s₂
  | `if e `then s₁ `else s₂ => `if exp_sub_exp σ e `then exp_sub_stm σ s₁ `else exp_sub_stm σ s₂
  end.

Local Close Scope stm_scope.
