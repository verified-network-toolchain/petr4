Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Section WeakestPre.
  Set Implicit Arguments.
  
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

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

  Definition preds (s: P4A.state_ref S) :=
    enum S.

  Definition pick_template (s: side) (c: conf_state S) : state_template S :=
    match s with
    | Left => c.(cs_st1)
    | Right => c.(cs_st2)
    end.
  
  Definition wp_edge (c: conf_rel S H) (s: side) (st: P4A.state S H) : store_rel H :=
    let st' := pick_template s c.(cr_st) in
    let tcond := trans_cond Left (P4A.st_trans st) st'.(st_state) in
    let wp_trans := BRImpl tcond c.(cr_rel) in
    wp_op s (P4A.st_op st) wp_trans.

  Definition wp_edges (c: conf_rel S H) (s_left: S) (s_right: S) : store_rel H :=
    let state_left := a.(P4A.t_states) s_left in
    let state_right := a.(P4A.t_states) s_right in
    let c' := {| cr_st := c.(cr_st);
                 cr_rel := wp_edge c Left state_left |} in
    wp_edge c' Right state_right.

  Definition wp_pred_pair (c: conf_rel S H) (preds: S * S) : conf_rel S H :=
    let '(sl, sr) := preds in
    {| cr_st := {| cs_st1 := {| st_state := inl sl;
                                st_buf_len := 0 |};
                   cs_st2 := {| st_state := inl sr;
                                st_buf_len := 0 |} |};
       cr_rel := wp_edges c (fst preds) (snd preds) |}.

  Definition wp (c: conf_rel S H) : list (conf_rel S H) :=
    let cur_st_left  := c.(cr_st).(cs_st1).(st_state) in
    let cur_st_right := c.(cr_st).(cs_st2).(st_state) in
    let pred_pairs := list_prod (preds cur_st_left)
                                (preds cur_st_right) in
    List.map (wp_pred_pair c) pred_pairs.

End WeakestPre.
