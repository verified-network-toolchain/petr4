From Poulet4 Require Import
  Utils.Util.FunUtil
  Utils.VecUtil
  P4cub.Syntax.AST P4cub.Syntax.CubNotations
  P4cub.Syntax.IndPrincip.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Export Coq.Arith.Compare_dec.
From Equations Require Import Equations.

Section Shift.
  Polymorphic Universe a.
  Variable A : Type@{a}.

  Polymorphic Definition shifter : Type@{a} := nat -> nat -> A -> A.
  
  Polymorphic Class Shift : Type@{a} := {
      shift : shifter;
      shift_0 : forall c a, shift c 0 a = a;
      shift_add : forall c m n a,
        shift c m (shift c n a) = shift c (m + n) a
    }.
End Shift.

Arguments shift {A}.
Arguments shift_0 {A}.
Arguments shift_add {A}.

Section ShiftVec.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universe a.

  Polymorphic Context {A : Type@{a}}.

  Section shift.
    Variables (sh : shifter A) (cutoff : nat).
    
    Section Shiftvec.
      Variable amt : nat.
      
      Polymorphic Equations shift_vec : forall {n : nat}, Vec.t A n -> Vec.t A n := {
          shift_vec []               := [];
          shift_vec (Vec.cons a n v) := sh (cutoff + n)%nat amt a :: shift_vec v }.
    End Shiftvec.
    
    Polymorphic Hypothesis sh_0 : forall c a, sh c 0 a = a.
    
    Polymorphic Lemma shift_vec_0 : forall {n} (v : Vec.t A n),
        shift_vec 0 v = v.
    Proof using A cutoff sh sh_0.
      intros n v.
      funelim (shift_vec 0 v).
      - rewrite shift_vec_equation_1. reflexivity.
      - rewrite shift_vec_equation_2.
        rewrite sh_0. f_equal. assumption.
    Qed.
    
    Polymorphic Hypothesis sh_add :
      forall c m n a, sh c m (sh c n a) = sh c (m + n) a.
    
    Polymorphic Lemma shift_vec_add : forall m n {o} (v : Vec.t A o),
        shift_vec m (shift_vec n v) = shift_vec (m + n) v.
    Proof using A cutoff sh sh_add.
      intros m n o v.
      funelim (shift_vec n v).
      - do 2 rewrite shift_vec_equation_1. reflexivity.
      - do 3 rewrite shift_vec_equation_2. cbn.
        rewrite sh_add. f_equal. auto.
    Qed.
  End shift.

  Polymorphic Global Instance Shift_vec {n} `(SH : Shift A) : Shift (Vec.t A n) :=
    { shift c a := shift_vec SH.(shift) c a (n:=n);
      shift_0 c := shift_vec_0 SH.(shift) c SH.(shift_0);
      shift_add c m q v := shift_vec_add SH.(shift) c SH.(shift_add) m q (o:=n) v
    }.
End ShiftVec.

Section ShiftList.
  Polymorphic Universe a.

  Polymorphic Context {A : Type@{a}}.

  Section shift.
    Polymorphic Variables (sh : shifter A) (cutoff : nat).

    Section Shiftlist.
      Variable amt : nat.
      
      Polymorphic Fixpoint shift_list (l : list A) : list A :=
        match l with
        | [] => []
        | h :: t => sh (cutoff + (length t)) amt h :: shift_list t
        end.
    End Shiftlist.

    Polymorphic Lemma shift_list_length : forall n l,
        length (shift_list n l) = length l.
    Proof using.
      intros n l; induction l as [| h t ih];
        cbn; f_equal; auto.
    Qed.

    Polymorphic Local Hint Rewrite shift_list_length : core.
    
    Polymorphic Hypothesis sh_0 : forall c a, sh c 0 a = a.
    
    Polymorphic Lemma shift_list_0 : forall (l : list A),
        shift_list 0 l = l.
    Proof using A cutoff sh sh_0.
      intro l; induction l as [| a l ih]; cbn; f_equal; auto.
    Qed.

    Polymorphic Hypothesis sh_add :
      forall c m n a, sh c m (sh c n a) = sh c (m + n) a.
    
    Polymorphic Lemma shift_list_add : forall m n (l : list A),
        shift_list m (shift_list n l) = shift_list (m + n) l.
    Proof using A cutoff sh sh_add.
      intros m n l.
      induction l as [| a l ih]; cbn;
        autorewrite with core;
        f_equal; eauto.
    Qed.
  End shift.

  Polymorphic Global Instance Shift_list `(SH : Shift A) : Shift (list A) :=
    { shift := shift_list SH.(shift);
      shift_0 c := shift_list_0 SH.(shift) c SH.(shift_0);
      shift_add c := shift_list_add SH.(shift) c SH.(shift_add)
    }.
End ShiftList.

Section Shift.
  Variables cutoff amt : nat.

  (** Updates cutoff. *)
  (*Definition smother (n : nat) : nat :=
    n + s.(cutoff)*)

  (*Definition boost (n : nat) : shifter :=
    s <| amt := n + s.(amt) |>.*)
  
  (*Definition shext : shifter :=
    smother 1.*)
  
  Definition shift_var (x : nat) : nat :=
    if le_lt_dec cutoff x then amt + x else x.
  
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

Section Shift.
  Variable c : nat.

  Lemma shift_exp_0 : forall e, shift_exp c 0 e = e.
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

  Lemma shift_exp_option_map_0 : forall oe,
      option_map (shift_exp c 0) oe = oe.
  Proof using.
    intros [e |]; unravel; autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_exp_option_map_0 : core.
  
  Lemma shift_exp_map_0 : forall es,
      map (shift_exp c 0) es = es.
  Proof using.
    intros es;
      induction es as [| e es ih]; unravel;
      autorewrite with core; f_equal; auto.
  Qed.

  Local Hint Rewrite shift_exp_map_0 : core.

  Lemma shift_arg_0 : forall arg, shift_arg c 0 arg = arg.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_arg_0 : core.

  Lemma shift_arg_map_0 : forall args,
      map (shift_arg c 0) args = args.
  Proof using.
    intros args;
      induction args as [| arg args ih];
      unravel; autorewrite with core;
      f_equal; auto.
  Qed.

  Local Hint Rewrite shift_arg_map_0 : core.
  
  Lemma shift_trns_0 : forall p, shift_trns c 0 p = p.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Lemma shift_call_0 : forall cl, shift_call c 0 cl = cl.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Variables m n : nat.

  Lemma shift_exp_add : forall e,
      shift_exp c m (shift_exp c n e)
      = shift_exp c (m + n) e.
  Proof using.
    intro e.
    induction e using custom_exp_ind; unravel; f_equal; auto.
    - unfold shift_var; cbn.
      repeat destruct_if; try lia.
    - rewrite map_map.
      apply map_ext_Forall.
      assumption.
  Qed.

  Local Hint Rewrite shift_exp_add : core.
  
  Lemma shift_arg_add : forall arg,
      shift_arg c m (shift_arg c n arg)
      = shift_arg c (m + n) arg.
  Proof using.
    intros [e | e | e]; unravel; autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_arg_add : core.
  
  Lemma shift_trns_add : forall t,
      shift_trns c m (shift_trns c n t)
      = shift_trns c (m + n) t.
  Proof using.
    intros [ | ]; unravel; autorewrite with core; reflexivity.
  Qed.

  Lemma shift_exp_option_map_add : forall oe,
      option_map (shift_exp c m) (option_map (shift_exp c n) oe)
      = option_map (shift_exp c (m + n)) oe.
  Proof using.
    intros []; unravel;
      autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_exp_option_map_add : core.
  
  Lemma shift_exp_map_add : forall es,
      map (shift_exp c m) (map (shift_exp c n) es)
      = map (shift_exp c (m + n)) es.
  Proof using.
    intros es;
      induction es as [| e es ih]; unravel;
      autorewrite with core; f_equal; auto.
  Qed.

  Local Hint Rewrite shift_exp_map_add : core.
  
  Lemma shift_arg_map_add : forall args,
      map (shift_arg c m) (map (shift_arg c n) args)
      = map (shift_arg c (m + n)) args.
  Proof using.
    intros args;
      induction args as [| arg args ih]; unravel;
      autorewrite with core; f_equal; auto.
  Qed.

  Lemma shift_call_add : forall cl,
      shift_call c m (shift_call c n cl)
      = shift_call c (m + n) cl.
  Proof using.
    intros []; unravel; autorewrite with core; reflexivity.
  Qed.
End Shift.

Global Instance Shift_exp : Shift Exp.t := {
    shift := shift_exp;
    shift_0 := shift_exp_0;
    shift_add := shift_exp_add
  }.

Global Instance Shift_arg : Shift (paramarg Exp.t Exp.t) := {
    shift := shift_arg;
    shift_0 := shift_arg_0;
    shift_add := shift_arg_add
  }.

Global Instance Shift_trns : Shift Trns.t := {
    shift := shift_trns;
    shift_0 := shift_trns_0;
    shift_add := shift_trns_add
  }.

Global Instance Shift_call : Shift Call.t := {
    shift := shift_call;
    shift_0 := shift_call_0;
    shift_add := shift_call_add
  }.

Local Open Scope stm_scope.

Fixpoint shift_stm
  (c a : nat) (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit => s
  | Stm.Ret oe
    => Stm.Ret $ option_map (shift_exp c a) oe
  | Stm.Trans e
    => Stm.Trans $ shift_trns c a e
  | e1 `:= e2 => shift_exp c a e1 `:= shift_exp c a e2
  | Stm.Invoke e t
    => Stm.Invoke (option_map (shift_exp c a) e) t
  | Stm.App fk args
    => Stm.App (shift_call c a fk) $ map (shift_arg c a) args
  |`let og := te `in b
    => `let og := map_sum id (shift_exp c a) te `in shift_stm (S c) a b
  | s₁ `; s₂ => shift_stm c a s₁ `; shift_stm c a s₂
  | `if e `then s₁ `else s₂
    => `if shift_exp c a e `then shift_stm c a s₁ `else shift_stm c a s₂
  end.

Definition shift_ctrl
  (c amt : nat) (d : Ctrl.t) : Ctrl.t :=
  match d with
  | Ctrl.Var x te => Ctrl.Var x $ map_sum id (shift_exp c amt) te
  | Ctrl.Action a cps dps s => Ctrl.Action a cps dps $ shift_stm c amt s
  | Ctrl.Table t key argss def =>
      Ctrl.Table
        t (map (fun '(e, mk) => (shift_exp c amt e, mk)) key)
        (map (fun '(a, args) => (a, map (shift_arg c amt) args)) argss)
        $ option_map (fun '(a, es) => (a, map (shift_exp c amt) es)) def
  end.

Fixpoint shift_ctrls
  (c a : nat) (ds : list Ctrl.t) : list Ctrl.t :=
  match ds with
  | [] => []
  | Ctrl.Var x te as d :: ds =>
      shift_ctrl c a d :: shift_ctrls (S c) a ds
  | d :: ds => shift_ctrl c a d :: shift_ctrls c a ds
  end.

Local Close Scope stm_scope.

Section Shiftstm.
  Local Hint Rewrite shift_exp_0 : core.
  Local Hint Rewrite shift_exp_map_0 : core.
  Local Hint Rewrite shift_arg_map_0 : core.
  Local Hint Rewrite shift_trns_0 : core.
  Local Hint Rewrite shift_call_0 : core.
  Local Hint Rewrite shift_exp_option_map_0 : core.
  
  Lemma shift_stm_0 : forall c s, shift_stm c 0 s = s.
  Proof using.
    intros c s;
      generalize dependent c;
      induction s;
      unravel;
      intro c;
      autorewrite with core;
      f_equal; auto.
    - destruct init; unravel;
        autorewrite with core; reflexivity.
  Qed.

  Local Hint Rewrite shift_exp_add : core.
  Local Hint Rewrite shift_exp_map_add : core.
  Local Hint Rewrite shift_arg_map_add : core.
  Local Hint Rewrite shift_trns_add : core.
  Local Hint Rewrite shift_call_add : core.
  Local Hint Rewrite shift_exp_option_map_add : core.

  Lemma shift_stm_add : forall c m n s,
      shift_stm c m (shift_stm c n s) = shift_stm c (m + n) s.
  Proof using.
    intros c m n s.
    generalize dependent c.
    induction s; intro c; unravel; autorewrite with core; f_equal; auto.
    destruct init; unravel; autorewrite with core; reflexivity.
  Qed.

  Global Instance Shift_stm : Shift Stm.t := {
      shift := shift_stm;
      shift_0 := shift_stm_0;
      shift_add := shift_stm_add
    }.
End Shiftstm.

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
  | Stm.Invoke e t => Stm.Invoke (option_map (exp_sub_exp σ) e) t
  | Stm.App fk args => Stm.App (exp_sub_call σ fk) $ List.map (exp_sub_arg σ) args
  | `let og := te `in s => `let og := map_sum id (exp_sub_exp σ) te `in exp_sub_stm (exts σ) s
  | s₁ `; s₂ => exp_sub_stm σ s₁ `; exp_sub_stm σ s₂
  | `if e `then s₁ `else s₂ => `if exp_sub_exp σ e `then exp_sub_stm σ s₁ `else exp_sub_stm σ s₂
  end.

Local Close Scope stm_scope.
