Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4cub.BigStep.BSUtil.
Require Poulet4.P4automata.P4automaton.
Module P4A := P4automaton.

Module Env := Poulet4.P4cub.Envn.Env.

Open Scope list_scope.

Section Syntax.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.

  Inductive hdr_ref: Type :=
  | HRVar (var: H).
  (*| HRField (hdr: hdr_ref) (field: string).*)

  Global Program Instance hdr_ref_eq_dec : EquivDec.EqDec hdr_ref eq :=
    { equiv_dec x y :=
        match x, y with
        | HRVar x, HRVar y => if x == y then in_left else in_right
        end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.
  
  Inductive expr :=
  | EHdr (h: hdr_ref)
  | ELit (bs: list bool).
  (* todo: binops, ...? *)
  
  Definition state_ref: Type := S + bool.
  
  Inductive v :=
  | VBits : list bool -> v.

  Global Program Instance v_eq_dec : EquivDec.EqDec v eq :=
    { equiv_dec :=
        fun x y =>
          match x, y with
          | VBits xs, VBits ys =>
            if xs == ys
            then in_left
            else in_right
          end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Record sel_case: Type :=
    { sc_val: v;
      sc_st: state_ref }.

  Inductive transition: Type :=
  | TGoto (state: state_ref)
  | TSel (cond: expr) (cases: list sel_case) (default: state_ref).

  Inductive op :=
  | OpNil
  | OpSeq (o1 o2: op)
  | OpExtract (width: nat) (hdr: hdr_ref)
  | OpAsgn (lhs: hdr_ref) (rhs: expr).

  Record state: Type :=
    { st_op: op;
      st_trans: transition }.

  Definition t: Type :=
    Env.t S state.

  Definition state_type (a: t) : Type :=
    { s: S | Env.find s a <> None :> option state }.

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

  Definition state_type_cons (a: t) (a': S * state)
    : state_type a -> state_type (a' :: a).
  Proof.
    unfold state_type.
    intros.
    destruct X.
    exists x.
    simpl.
    destruct a'.
    destruct (_ x s); congruence.
  Defined.

  Definition list_states (a: t) : list (state_type a).
  Proof.
    revert a.
    induction a.
    - exact nil.
    - assert (Env.find (fst a) (a :: a0) <> None).
      {
        destruct a.
        simpl.
        autorewrite with core.
        congruence.
      }
      apply cons.
      + exists (fst a); auto.
      + apply (List.map (state_type_cons a)).
        apply IHa.
  Defined.

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
    
  Definition expr_fmapH (e: expr H) : expr H' :=
    match e with
    | EHdr h => EHdr (hdr_ref_fmapH h)
    | ELit _ bs => ELit _ bs
    end.
  
  Definition state_ref_fmapS (s: state_ref S) : state_ref S' :=
    match s with
    | inl s' => inl (f s')
    | inr r => inr r
    end.

  Definition sel_case_fmapS (c: sel_case S) : sel_case S' :=
    {| sc_val := c.(sc_val);
       sc_st := state_ref_fmapS c.(sc_st) |}.

  Definition transition_fmapSH (t: transition S H) : transition S' H' :=
    match t with
    | TGoto _ s => TGoto _ (state_ref_fmapS s)
    | TSel expr cases default =>
      TSel (expr_fmapH expr) (List.map sel_case_fmapS cases) (state_ref_fmapS default)
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

  Definition t_fmapSH (a: t S H) : t S' H' :=
    Env.map_keys f (Env.map_vals state_fmapSH a).
End Fmap.

Definition t_fmapH {S H H'} (f: H -> H') (a: t S H) : t S H' :=
  t_fmapSH id f a.

Definition t_fmapS {S H S'} (f: S -> S') (a: t S H) : t S' H :=
  t_fmapSH f id a.

Section Interp.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eqdec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eqdec: EquivDec.EqDec H eq}.

  Variable (a: t S H).

  Definition list_states' : list S :=
    List.map fst a.

  Definition store := Env.t H v.
  
  Fixpoint op_size (o: op H) : nat :=
    match o with
    | OpNil _ => 0
    | OpSeq o1 o2 =>
      op_size o1 + op_size o2
    | OpExtract width _ => width
    | OpAsgn _ _ => 0
    end.

  Definition find_state (st: state_type a) : state S H.
  Proof.
    destruct (Env.find (proj1_sig st) a) eqn:?.
    - exact s.
    - exfalso.
      apply (proj2_sig st).
      apply Heqo.
  Defined.

  Definition size (state: state_type a) : nat :=
    op_size (find_state state).(st_op).

  Variable (has_extract: forall s h, 0 < size (exist _ s h)).

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

  Definition eval_expr (st: store) (e: expr H) : v :=
   match e with
   | EHdr (HRVar x) =>
     match Env.find x st with
     | Some v => v
     | None => VBits nil
     end
   | ELit _ bs => VBits bs
   end.

  Fixpoint eval_op (st: store) (bits: list bool) (o: op H) : store :=
    match o with
    | OpNil _ => st
    | OpSeq o1 o2 =>
      eval_op (eval_op st bits o1) bits o2
    | OpExtract width hdr =>
      assign hdr (VBits (List.firstn width bits)) st
    | OpAsgn hdr expr =>
      assign hdr (eval_expr st expr) st
    end.

  Definition update (state: state_type a) (bits: list bool) (st: store) : store :=
    eval_op st bits (find_state state).(st_op).
  
  Fixpoint pre_eval_sel (st: store) (cond: v) (cases: list (sel_case S)) (default: state_ref S) : state_ref S :=
    match cases with
    | c::cases =>
      if cond == c.(sc_val)
      then c.(sc_st)
      else pre_eval_sel st cond cases default
    | nil => default
    end.

  Definition clamp_state_name (s: S) : state_type a + bool.
  Proof.
    destruct (Env.find s a) eqn:?.
    - left.
      exists s.
      congruence.
    - exact (inr false).
  Defined.

  Definition clamp_state_ref (s: state_ref S) : state_type a + bool :=
    match s with
    | inl s => clamp_state_name s
    | inr b => inr b
    end.
  
  Definition eval_sel (st: store) (cond: v) (cases: list (sel_case S)) (default: state_ref S) : state_type a + bool :=
    clamp_state_ref (pre_eval_sel st cond cases default).

  Definition eval_trans (st: store) (t: transition S H) : state_type a + bool :=
    match t with
    | TGoto _ state => clamp_state_ref state
    | TSel cond cases default =>
      eval_sel st (eval_expr st cond) cases default
    end.

  Definition transitions (s: state_type a) (st: store) : state_type a + bool :=
    eval_trans st (find_state s).(st_trans).

  Lemma cap: forall s, 0 < size s.
  Proof.
    intros.
    destruct s.
    apply has_extract.
  Qed.
  
  Definition interp : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := state_type a;
       P4A.size := size;
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := cap |}.
End Interp.

Section Inline.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.


  Definition inline (pref: S) (suff: S) (auto: t S H) : t S H := 
    match Env.find pref auto with 
    | Some (Build_state op (TGoto _ (inl nxt))) => 
      if nxt == suff 
      then 
      let pref' := 
        match Env.find suff auto with 
        | Some suff_st => {| st_op := OpSeq op (st_op suff_st); st_trans := st_trans suff_st |}
        | None => {| st_op := op ; st_trans := TGoto _ (inl nxt) |}
        end in 
      Env.bind pref pref' auto
      else auto
    | _ => auto
    end.

  (* Lemma inline_corr : 
    forall pref suff auto (s: store), 
      let start_config : P4A.configuration (interp _ _ auto) := (SNStart, s, nil) in 
      True. *)

End Inline.
