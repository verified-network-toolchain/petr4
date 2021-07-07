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
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Variable (a: P4A.t S H).

  Fixpoint expr_to_bit_expr {c} (s: side) (e: P4A.expr H) : bit_expr H c :=
    match e with
    | P4A.EHdr h => BEHdr c s h
    | P4A.ELit _ bs => BELit _ c bs
    | P4A.ESlice e hi lo => BESlice (expr_to_bit_expr s e) hi lo
    end.

  Definition val_to_bit_expr {c} (value: P4A.v) : bit_expr H c :=
    match value with
    | P4A.VBits bs => BELit _ c bs
    end.

  Fixpoint be_subst {c} (be: bit_expr H c) (e: bit_expr H c) (x: bit_expr H c) : bit_expr H c :=
    match be with
    | BELit _ _ l => BELit _ _ l
    | BEBuf _ _ _
    | BEHdr _ _ _
    | BEVar _ _ =>
      if bit_expr_eq_dec be x then e else be
    | BESlice be hi lo => beslice (be_subst be e x) hi lo
    | BEConcat e1 e2 => beconcat (be_subst e1 e x) (be_subst e2 e x)
    end.

  Fixpoint sr_subst {c} (sr: store_rel H c) (e: bit_expr H c) (x: bit_expr H c) : store_rel H c :=
  match sr with
  | BRTrue _ _
  | BRFalse _ _ => sr
  | BREq e1 e2 => BREq (be_subst e1 e x) (be_subst e2 e x)
  | BRAnd r1 r2 => brand (sr_subst r1 e x) (sr_subst r2 e x)
  | BROr r1 r2 => bror (sr_subst r1 e x) (sr_subst r2 e x)
  | BRImpl r1 r2 => brimpl (sr_subst r1 e x) (sr_subst r2 e x)
  end.

  Fixpoint pat_cond {ctx: bctx} (si: side) (p: P4A.pat) (c: P4A.cond H) : store_rel H ctx :=
    match p, c with
    | P4A.PExact val, P4A.CExpr e =>
      BREq (expr_to_bit_expr si e) (val_to_bit_expr val)
    | P4A.PAny, _ => BRTrue _ _
    | P4A.PPair p1 p2, P4A.CPair e1 e2 =>
      BRAnd (pat_cond si p1 e1) (pat_cond si p2 e2)
    | _, _ => BRFalse _ _
    end.
  
  Definition case_cond {ctx: bctx} (si: side) (cn: Syntax.cond H) (st': P4A.state_ref S) (s: P4A.sel_case S) : store_rel H ctx :=
    if st' == P4A.sc_st s
    then pat_cond si s.(P4A.sc_pat) cn
    else BRFalse _ _.

  Definition cases_cond {ctx: bctx} (si: side) (cond: Syntax.cond H) (st': P4A.state_ref S) (s: list (P4A.sel_case S)) : store_rel H ctx :=
    List.fold_right (@bror _ _) (BRFalse _ _) (List.map (case_cond si cond st') s).

  Definition trans_cond
             {c: bctx}
             (s: side)
             (t: P4A.transition S H)
             (st': P4A.state_ref S)
    : store_rel H c :=
    match t with
    | P4A.TGoto _ r =>
      if r == st'
      then BRTrue _ _
      else BRFalse _ _
    | P4A.TSel cond cases default =>
      let any_case := cases_cond s cond st' cases in
      bror any_case
           (if default == st'
            then (brimpl any_case (BRFalse _ _))
            else BRFalse _ _)
    end.

  Fixpoint wp_op' {c} (s: side) (o: P4A.op H) : nat * store_rel H c -> nat * store_rel H c :=
    fun '(buf_hi_idx, phi) =>
      match o with
      | P4A.OpNil _ => (buf_hi_idx, phi)
      | P4A.OpSeq o1 o2 =>
        wp_op' s o1 (wp_op' s o2 (buf_hi_idx, phi))
      | P4A.OpExtract width hdr =>
        let new_idx := buf_hi_idx - width in
        let slice := beslice (BEBuf _ _ s) (buf_hi_idx - 1) new_idx in
        (new_idx, sr_subst phi slice (BEHdr _ s hdr))
      | P4A.OpAsgn lhs rhs =>
        (buf_hi_idx, sr_subst phi (expr_to_bit_expr s rhs) (BEHdr _ s lhs))
      end.

  Definition wp_op {c} (s: side) (o: P4A.op H) (phi: store_rel H c) : store_rel H c :=
    snd (wp_op' s o (P4A.op_size o, phi)).

  Inductive pred (c: bctx) :=
  | PredRead (s: state_template S)
  | PredJump (cond: store_rel H c) (s: P4A.state_ref S).

  Definition weaken_pred {c} (size: nat) (p: pred c) : pred (BCSnoc c size) :=
    match p with
    | PredRead _ s => PredRead _ s
    | PredJump cond s => PredJump (weaken_store_rel size cond) s
    end.

  Definition pick_template (s: side) (c: conf_state S) : state_template S :=
    match s with
    | Left => c.(cs_st1)
    | Right => c.(cs_st2)
    end.

  Definition preds {c} (si: side) (candidates: list (P4A.state_ref S)) (s: state_template S) : list (pred c) :=
    if s.(st_buf_len) == 0
    then List.map (fun candidate =>
                     match candidate with
                     | inl cand =>
                       let st := a.(P4A.t_states) cand in
                       PredJump (trans_cond si (P4A.st_trans st) s.(st_state)) candidate
                     | inr _ =>
                       PredJump
                         (match s.(st_state) with
                          | inr false => BRTrue _ _
                          | _ => BRFalse _ _
                          end)
                         candidate
                     end)
                  candidates
    else [PredRead _ {| st_state := s.(st_state); st_buf_len := s.(st_buf_len) - 1 |}].

  Definition wp_pred {c: bctx} (si: side) (b: bit_expr H c) (p: pred c) (phi: store_rel H c) : store_rel H c :=
    match p with
    | PredRead _ s =>
      sr_subst phi (beconcat (BEBuf _ _ si) b) (BEBuf _ _ si)
    | PredJump cond (inl s) =>
      (sr_subst (wp_op si (a.(P4A.t_states) s).(P4A.st_op)
                                                 (brimpl cond phi))
                (beconcat (BEBuf _ _ si) b)
                (BEBuf _ _ si))
    | PredJump cond (inr s) =>
      brimpl cond (sr_subst phi
                            (BELit _ _ [])
                            (BEBuf _ _ si))
    end.

  Definition st_pred {c} (p: pred c) :=
    match p with
    | PredRead _ s => s
    | PredJump _ s => {| st_state := s;
                         st_buf_len := P4A.P4A.size' (a:=P4A.interp a) s - 1 |}
    end.

  Definition wp_pred_pair (phi: conf_rel S H) (preds: pred phi.(cr_ctx) * pred phi.(cr_ctx)) : list (conf_rel S H) :=
    let '(sl, sr) := preds in
    [{| cr_st := {| cs_st1 := st_pred sl;
                    cs_st2 := st_pred sr |};
        cr_rel := wp_pred Left (BELit _ _ [false]) sl
                          (wp_pred Right (BELit _ _ [false]) sr phi.(cr_rel)) |};
     {| cr_st := {| cs_st1 := st_pred sl;
                    cs_st2 := st_pred sr |};
        cr_rel := wp_pred Left (BELit _ _ [true]) sl
                          (wp_pred Right (BELit _ _ [true]) sr phi.(cr_rel)) |}].
     
  Definition wp (phi: conf_rel S H) : list (conf_rel S H) :=
    let cur_st_left  := phi.(cr_st).(cs_st1) in
    let cur_st_right := phi.(cr_st).(cs_st2) in
    let pred_pairs := list_prod (preds Left ([inr false; inr true] ++ List.map (fun s => inl (inl s)) (enum S1)) cur_st_left)
                                (preds Right ([inr false; inr true] ++ List.map (fun s => inl (inr s)) (enum S2)) cur_st_right) in
    List.concat (List.map (wp_pred_pair phi) pred_pairs).

End WeakestPre.
