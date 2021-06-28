Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Import ListNotations.

Section WeakestPre.
  Set Implicit Arguments.
  
  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Definition S: Type := S1 + S2.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.

  Variable (a: P4A.t S H).

  Definition expr_to_bit_expr (s: side) (e: P4A.expr H) : bit_expr H :=
    match e with
    | P4A.EHdr h => BEHdr s h
    | P4A.ELit _ bs => BELit _ bs
    end.

  Definition val_to_bit_expr (value: P4A.v) : bit_expr H :=
    match value with
    | P4A.VBits bs => BELit _ bs
    end.

  Definition case_cond (cond: bit_expr H) (st': P4A.state_ref S) (s: P4A.sel_case S) :=
    if st' == P4A.sc_st s
    then BREq cond (val_to_bit_expr (P4A.sc_val s))
    else BRFalse _.

  Definition cases_cond (cond: bit_expr H) (st': P4A.state_ref S) (s: list (P4A.sel_case S)) :=
    List.fold_right (@BROr H) (BRFalse _) (List.map (case_cond cond st') s).

  Fixpoint case_negated_conds (cond: bit_expr H) (s: list (P4A.sel_case S)) :=
    match s with
    | nil => BRTrue _
    | s :: rest =>
      BRAnd
        (BRNotEq cond (val_to_bit_expr (P4A.sc_val s)))
        (case_negated_conds cond rest)
    end.

  Definition trans_cond (s: side) (t: P4A.transition S H) (st': P4A.state_ref S) :=
    match t with
    | P4A.TGoto _ r =>
      if r == st'
      then BRTrue _
      else BRFalse _
    | P4A.TSel cond cases default =>
      let be_cond := expr_to_bit_expr s cond in
      BROr (cases_cond be_cond st' cases)
           (if default == st'
            then case_negated_conds be_cond cases
            else BRFalse _)
    end.

  Fixpoint bit_expr_subst (s: side) (h: P4A.hdr_ref H) (exp: bit_expr H) (phi: bit_expr H) : bit_expr H :=
    match phi with
    | BELit _ _
    | BEBuf _ _ => phi
    | BEHdr s' h' =>
      if andb (s ==b s') (h ==b h')
      then exp
      else phi
    | BESlice e hi lo =>
      BESlice (bit_expr_subst s h exp e) hi lo
    | BEConcat e1 e2 =>
      BEConcat (bit_expr_subst s h exp e1)
               (bit_expr_subst s h exp e2)
    end.

  Fixpoint store_rel_subst (s: side) (h: P4A.hdr_ref H) (exp: bit_expr H) (phi: store_rel H) : store_rel H :=
    match phi with
    | BRTrue _
    | BRFalse _ =>
      phi
    | BREq e1 e2 =>
      BREq (bit_expr_subst s h exp e1)
           (bit_expr_subst s h exp e2)
    | BRNotEq e1 e2 =>
      BRNotEq (bit_expr_subst s h exp e1)
              (bit_expr_subst s h exp e2)
    | BRAnd r1 r2 =>
      BRAnd (store_rel_subst s h exp r1)
            (store_rel_subst s h exp r2)
    | BROr r1 r2 =>
      BROr (store_rel_subst s h exp r1)
           (store_rel_subst s h exp r2)
    | BRImpl r1 r2 =>
      BRImpl (store_rel_subst s h exp r1)
             (store_rel_subst s h exp r2)
    end.

  Fixpoint wp_op' (s: side) (o: P4A.op H) : nat * store_rel H -> nat * store_rel H :=
    fun '(buf_idx, phi) =>
      match o with
      | P4A.OpNil _ => (buf_idx, phi)
      | P4A.OpSeq o1 o2 =>
        wp_op' s o1 (wp_op' s o2 (buf_idx, phi))
      | P4A.OpExtract width hdr =>
        let new_idx := buf_idx + width - 1 in
        let slice := BESlice (BEBuf _ s) new_idx buf_idx in
        (new_idx, store_rel_subst s hdr slice phi)
      | P4A.OpAsgn lhs rhs =>
        (buf_idx, store_rel_subst s lhs (expr_to_bit_expr s rhs) phi)
      end.

  Definition wp_op (s: side) (o: P4A.op H) (phi: store_rel H) : store_rel H :=
    snd (wp_op' s o (0, phi)).

  Inductive pred :=
  | PredRead (s: state_template S)
  | PredJump (cond: store_rel H) (s: S).

  Definition pick_template (s: side) (c: conf_state S) : state_template S :=
    match s with
    | Left => c.(cs_st1)
    | Right => c.(cs_st2)
    end.

  Definition preds (si: side) (candidates: list S) (s: state_template S) : list pred :=
    if s.(st_buf_len) == 0
    then [PredRead {| st_state := s.(st_state); st_buf_len := s.(st_buf_len) - 1 |}]
    else List.map (fun candidate =>
                     let st := a.(P4A.t_states) candidate in
                     PredJump (trans_cond si (P4A.st_trans st) s.(st_state)) candidate)
                  candidates.

  Definition sr_subst (sr: store_rel H) (e: bit_expr H) (x: bit_expr H) : store_rel H.
  Admitted.

  Definition be_subst (be: bit_expr H) (e: bit_expr H) (x: bit_expr H) : bit_expr H.
  Admitted.

  Definition wp_pred (si: side) (b: bool) (p: pred) (c: store_rel H) : store_rel H :=
    let phi := sr_subst c (BEConcat (BEBuf _ si) (BELit _ [b])) (BEBuf _ si) in
    match p with
    | PredRead s =>
      phi
    | PredJump cond s =>
      BRImpl cond
             (wp_op si (a.(P4A.t_states) s).(P4A.st_op) phi)
    end.

  Definition st_pred (p: pred) :=
    match p with
    | PredRead s => s
    | PredJump _ s => {| st_state := inl s; st_buf_len := 0 |}
    end.

  Definition wp_pred_pair (c: conf_rel S H) (preds: pred * pred) : list (conf_rel S H) :=
    let '(sl, sr) := preds in
    [{| cr_st := {| cs_st1 := st_pred sl;
                    cs_st2 := st_pred sr |};
        cr_rel := wp_pred Left false sl (wp_pred Right false sr c.(cr_rel)) |};
     {| cr_st := {| cs_st1 := st_pred sl;
                    cs_st2 := st_pred sr |};
        cr_rel := wp_pred Left false sl (wp_pred Right false sr c.(cr_rel)) |}].
     
  Definition wp (c: conf_rel S H) : list (conf_rel S H) :=
    let cur_st_left  := c.(cr_st).(cs_st1) in
    let cur_st_right := c.(cr_st).(cs_st2) in
    let pred_pairs := list_prod (preds Left (List.map inl (enum S1)) cur_st_left)
                                (preds Right (List.map inr (enum S2)) cur_st_right) in
    List.concat (List.map (wp_pred_pair c) pred_pairs).

End WeakestPre.
