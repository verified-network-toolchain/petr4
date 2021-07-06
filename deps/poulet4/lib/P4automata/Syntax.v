Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.HAList.
Require Import Poulet4.FinType.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4automata.P4automaton.
Module P4A := P4automaton.

Module Env := Poulet4.P4cub.Envn.Env.

Open Scope list_scope.

Section Syntax.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Inductive hdr_ref: Type :=
  | HRVar (var: H).
  (*| HRField (hdr: hdr_ref) (field: string).*)
  Derive NoConfusion for hdr_ref.
  Global Program Instance hdr_ref_eq_dec : EquivDec.EqDec hdr_ref eq :=
    { equiv_dec x y :=
        match x, y with
        | HRVar x, HRVar y => if x == y then in_left else in_right
        end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.
  
  Inductive expr :=
  | EHdr (h: hdr_ref)
  | ELit (bs: list bool)
  | ESlice (e: expr) (hi lo: nat).
  (* todo: binops, ...? *)
  
  Definition state_ref: Type := S + bool.
  
  Inductive v :=
  | VBits : list bool -> v.

  Global Program Instance v_eq_dec : EquivDec.EqDec v eq :=
    { equiv_dec x y :=
        match x, y with
        | VBits xs, VBits ys =>
          if xs == ys
          then in_left
          else in_right
        end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Inductive pat :=
  | PExact (val: v)
  | PAny
  | PPair (p1: pat) (p2: pat).

  Inductive cond :=
  | CExpr (e: expr)
  | CPair (c1: cond) (c2: cond).

  Record sel_case: Type :=
    { sc_pat: pat;
      sc_st: state_ref }.

  Inductive transition: Type :=
  | TGoto (state: state_ref)
  | TSel (c: cond) (cases: list sel_case) (default: state_ref).

  Inductive op :=
  | OpNil
  | OpSeq (o1 o2: op)
  | OpExtract (width: nat) (hdr: hdr_ref)
  | OpAsgn (lhs: hdr_ref) (rhs: expr).
  
  Fixpoint op_size (o: op) : nat :=
    match o with
    | OpNil => 0
    | OpSeq o1 o2 =>
      op_size o1 + op_size o2
    | OpExtract width _ => width
    | OpAsgn _ _ => 0
    end.

  Fixpoint nonempty (o: op) : Prop :=
    match o with
    | OpAsgn _ _
    | OpNil => True
    | OpSeq o1 o2 => nonempty o1 /\ nonempty o2
    | OpExtract width hdr => width > 0
    end.

  Record state: Type :=
    { st_op: op;
      st_trans: transition }.

  Definition state_size (st: state) : nat :=
    op_size st.(st_op).

  Record t: Type :=
    { t_states: S -> state;
      t_nonempty: forall s, nonempty (t_states s).(st_op);
      t_has_extract: forall s, state_size (t_states s) > 0 }.

  Program Definition bind (s: S) (st: state) (ex: state_size st > 0) (ok: nonempty st.(st_op)) (a: t) :=
    {| t_states := fun s' => if s == s' then st else a.(t_states) s' |}.
  Next Obligation.
    destruct (s == s0).
    - auto.
    - eapply a.(t_nonempty).
  Qed.
  Next Obligation.
    destruct (s == s0).
    - auto.
    - eapply a.(t_has_extract).
  Qed.

  Definition size (a: t) (s: S) :=
    state_size (a.(t_states) s).

  Lemma eq_dec_refl (A: Type) (eq_dec: forall x y : A, {x = y} + {x <> y}) :
    forall x,
      eq_dec x x = left eq_refl.
  Proof using.
    intros.
    pose proof (@Eqdep_dec.UIP_dec A eq_dec x x eq_refl).
    destruct (eq_dec x x).
    - erewrite H0; eauto.
    - congruence.
  Qed.
  Hint Rewrite eq_dec_refl : core.

End Syntax.

Section Fmap.
  Set Implicit Arguments.
  Variables (S H S' H': Type).
  Variable (f: S -> S').
  Variable (g: H -> H').

  Definition hdr_ref_fmapH (h: hdr_ref H) : hdr_ref H' :=
    match h with
    | HRVar h => HRVar (g h)
    end.
    
  Fixpoint expr_fmapH (e: expr H) : expr H' :=
    match e with
    | EHdr h => EHdr (hdr_ref_fmapH h)
    | ELit _ bs => ELit _ bs
    | ESlice e hi lo => ESlice (expr_fmapH e) hi lo
    end.
  
  Definition state_ref_fmapS (s: state_ref S) : state_ref S' :=
    match s with
    | inl s' => inl (f s')
    | inr r => inr r
    end.

  Definition sel_case_fmapS (c: sel_case S) : sel_case S' :=
    {| sc_pat := c.(sc_pat);
       sc_st := state_ref_fmapS c.(sc_st) |}.

  Fixpoint cond_fmapH (c: cond H) : cond H' :=
    match c with
    | CExpr e => CExpr (expr_fmapH e)
    | CPair c1 c2 => CPair (cond_fmapH c1) (cond_fmapH c2)
    end.

  Definition transition_fmapSH (t: transition S H) : transition S' H' :=
    match t with
    | TGoto _ s => TGoto _ (state_ref_fmapS s)
    | TSel cond cases default =>
      TSel (cond_fmapH cond) (List.map sel_case_fmapS cases) (state_ref_fmapS default)
    end.

  Fixpoint op_fmapH (o: op H) : op H' :=
    match o with
    | OpNil _ => OpNil _
    | OpSeq o1 o2 => OpSeq (op_fmapH o1) (op_fmapH o2)
    | OpExtract width hdr => OpExtract width (hdr_ref_fmapH hdr)
    | OpAsgn lhs rhs => OpAsgn (hdr_ref_fmapH lhs) (expr_fmapH rhs)
    end.

  Definition state_fmapSH (s: state S H) : state S' H' :=
    {| st_op := op_fmapH s.(st_op);
       st_trans := transition_fmapSH s.(st_trans) |}.

  Lemma op_fmapH_size :
    forall o,
      op_size (op_fmapH o) = op_size o.
  Proof.
    induction o; simpl; eauto.
  Qed.

  Lemma state_fmapSH_size :
    forall s,
      state_size (state_fmapSH s) = state_size s.
  Proof.
    unfold state_size.
    simpl; eauto using op_fmapH_size.
  Qed.

  Lemma op_fmapH_nonempty :
    forall o,
      nonempty (op_fmapH o) <-> nonempty o.
  Proof.
    induction o; simpl; intuition.
  Qed.

End Fmap.

Section Interp.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eqdec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eqdec: EquivDec.EqDec H eq}.

  Variable (a: t S H).

  Definition store := Env.t H v.
  
  Definition assign (h: hdr_ref H) (v: v) (st: store) : store :=
    match h with
    | HRVar x => Env.bind x v st
    end.

  Definition find (h: hdr_ref H) (st: store) : v :=
    match h with
    | HRVar x =>
      match Env.find x st with
      | Some v => v
      | None => VBits nil
      end
    end.

  Definition slice {A} (l: list A) (hi lo: nat) :=
    List.skipn lo (List.firstn (1 + hi) l).

  Fixpoint eval_expr (st: store) (e: expr H) : v :=
   match e with
   | EHdr (HRVar x) =>
     match Env.find x st with
     | Some v => v
     | None => VBits nil
     end
   | ELit _ bs =>
     VBits bs
   | ESlice e hi lo =>
     let '(VBits bs) := eval_expr st e in
     VBits (slice bs hi lo)
   end.

  Fixpoint eval_op (st: store) (idx: nat) (bits: list bool) (o: op H) : store * nat :=
    match o with
    | OpNil _ => (st, idx)
    | OpSeq o1 o2 =>
      let '(st, idx) := eval_op st idx bits o1 in
      eval_op st idx bits o2
    | OpExtract width hdr =>
      (assign hdr (VBits (List.firstn width (List.skipn idx bits))) st, idx + width)
    | OpAsgn hdr expr =>
      (assign hdr (eval_expr st expr) st, idx)
    end.

  Definition update (state: S) (bits: list bool) (st: store) : store :=
    fst (eval_op st 0 bits (a.(t_states) state).(st_op)).

  Fixpoint match_pat (st: store) (c: cond H) (p: pat) :=
    match c, p with
    | CExpr e, PAny =>
      true
    | CExpr e, PExact v =>
      if eval_expr st e == v then true else false
    | CPair c1 c2, PPair p1 p2 =>
      andb (match_pat st c1 p1) (match_pat st c2 p2)
    | _, _ => false
    end.

  Fixpoint eval_sel (st: store) (c: cond H) (cases: list (sel_case S)) (default: state_ref S) : state_ref S :=
    match cases with
    | sc::cases =>
      if match_pat st c sc.(sc_pat)
      then sc.(sc_st)
      else eval_sel st c cases default
    | nil => default
    end.

  Definition eval_trans (st: store) (t: transition S H) : state_ref S :=
    match t with
    | TGoto _ state => state
    | TSel cond cases default =>
      eval_sel st cond cases default
    end.

  Definition transitions (s: S) (st: store) : state_ref S :=
    eval_trans st (a.(t_states) s).(st_trans).

  Definition interp : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := S;
       P4A.size := size a;
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := a.(t_has_extract) |}.
End Interp.

Section Inline.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.


  Program Definition inline (pref: S) (suff: S) (auto: t S H) : t S H := 
    match auto.(t_states) pref with 
    | Build_state op (TGoto _ (inl nxt)) => 
      if nxt == suff 
      then 
      let pref' := 
        match auto.(t_states) suff with 
        | suff_st => {| st_op := OpSeq op (st_op suff_st); st_trans := st_trans suff_st |}
        end in 
      bind pref pref' _ _ auto
      else auto
    | _ => auto
    end.
  Next Obligation.
    pose proof auto.(t_has_extract) suff.
    unfold state_size in *.
    simpl in *.
    Lia.lia.
  Qed.
  Next Obligation.
    pose proof auto.(t_nonempty) suff.
    pose proof auto.(t_nonempty) pref.
    rewrite <- Heq_anonymous in * |-.
    simpl in *.
    intuition.
  Qed.

  (* Lemma inline_corr : 
    forall pref suff auto (s: store), 
      let start_config : P4A.configuration (interp _ _ auto) := (SNStart, s, nil) in 
      True. *)

End Inline.
