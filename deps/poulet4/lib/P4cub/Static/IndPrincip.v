Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Static.Util
        Poulet4.P4cub.Static.Typing.

Import P.P4cubNotations Env.EnvNotations.

(** Custom induction principle for expression typing. *)
Section CheckExprInduction.
  Variable (tags_t : Type).
  
  (** An arbitrary predicate. *)
  Variable P : errors -> gamma -> E.e tags_t -> E.t -> Prop.
  
  Hypothesis HBool : forall errs Γ b i,
      P errs Γ <{ BOOL b @ i }> {{ Bool }}.
  (**[]*)
  
  Hypothesis HBit : forall errs Γ w n i,
      BitArith.bound w n ->
      P errs Γ <{ w W n @ i }> {{ bit<w> }}.
  (**[]*)
  
  Hypothesis HInt : forall errs Γ w z i,
      IntArith.bound w z ->
      P errs Γ <{ w S z @ i }> {{ int<w> }}.
  (**[]*)
  
  Hypothesis HVar : forall errs Γ x τ i,
      Env.find x Γ = Some τ ->
      PT.proper_nesting τ ->
      P errs Γ <{ Var x:τ @ i }> τ.
  (**[]*)
  
  Hypothesis HSlice : forall errs Γ e τ hi lo w i,
      (lo <= hi < w)%positive ->
      numeric_width w τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      P errs Γ e τ ->
      let w' := (hi - lo + 1)%positive in
      P errs Γ <{ Slice e:τ [hi:lo] @ i }> {{ bit<w'> }}.
  (**[]*)
  
  Hypothesis HCast : forall errs Γ τ τ' e i,
      proper_cast τ' τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ' ->
      P errs Γ e τ' ->
      P errs Γ <{ Cast e:τ @ i }> τ.
  (**[]*)
  
  Hypothesis HUop : forall errs Γ op τ τ' e i,
      uop_type op τ τ' ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      P errs Γ e τ ->
      P errs Γ <{ UOP op e:τ @ i }> τ'.
  
  Hypothesis HBop : forall errs Γ op τ1 τ2 τ e1 e2 i,
      bop_type op τ1 τ2 τ ->
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ1 ->
      P errs Γ e1 τ1 ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ2 ->
      P errs Γ e2 τ2 ->
      P errs Γ <{ BOP e1:τ1 op e2:τ2 @ i }> τ.
  
  Hypothesis HMem : forall errs Γ e x fs τ τ' i,
      F.get x fs = Some τ' ->
      member_type fs τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      P errs Γ e τ ->
      P errs Γ <{ Mem e:τ dot x @ i }> τ'.
  (**[]*)
  
  Hypothesis HTuple : forall errs Γ es i ts,
      Forall2 (fun e τ => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es ts ->
      Forall2 (P errs Γ) es ts ->
      P errs Γ <{ tup es @ i }> {{ tuple ts }}.
  (**[]*)
  
  Hypothesis HStructLit : forall errs Γ efs tfs i,
      F.relfs
        (fun te τ =>
           (fst te) = τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      F.relfs
        (fun te τ => let e := snd te in P errs Γ e τ)
        efs tfs ->
      P errs Γ <{ struct { efs } @ i }> {{ struct { tfs } }}.
  (**[]*)
  
  Hypothesis HHdrLit : forall errs Γ efs tfs i b,
      PT.proper_nesting {{ hdr { tfs } }} ->
      F.relfs
        (fun te τ =>
           (fst te) = τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      F.relfs
        (fun te τ => let e := snd te in P errs Γ e τ)
        efs tfs ->
      ⟦ errs, Γ ⟧ ⊢ b ∈ Bool ->
      P errs Γ b {{ Bool }} ->
      P errs Γ <{ hdr { efs } valid:=b @ i }> {{ hdr { tfs } }}.
  (**[]*)
  
  Hypothesis HError : forall errs Γ err i,
      error_ok errs err ->
      P errs Γ <{ Error err @ i }> {{ error }}.
  (**[]*)
  
  Hypothesis HMatchKind : forall errs Γ mkd i,
      P errs Γ <{ Matchkind mkd @ i }> {{ matchkind }}.
  (**[]*)
  
  Hypothesis HStack : forall errs Γ ts hs n ni i,
      BitArith.bound 32%positive (Zpos n) ->
      (0 <= ni < (Zpos n))%Z ->
      Pos.to_nat n = length hs ->
      PT.proper_nesting {{ stack ts[n] }} ->
      Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
      Forall (fun e => P errs Γ e {{ hdr { ts } }}) hs ->
      P errs Γ <{ Stack hs:ts[n] nextIndex:=ni @ i }> {{ stack ts[n] }}.
  (**[]*)
  
  Hypothesis HAccess : forall errs Γ e idx i ts n,
      (0 <= idx < (Zpos n))%Z ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ stack ts[n] ->
      P errs Γ e {{ stack ts[n] }} ->
      P errs Γ <{ Access e[idx] @ i }> {{ hdr { ts } }}.
  (**[]*)
  
  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_check_expr_ind]. *)
  Definition custom_check_expr_ind :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t) (τ : E.t)
      (HY : ⟦ errs, Γ ⟧ ⊢ e ∈ τ), P errs Γ e τ :=
    fix chind errs Γ e τ HY :=
      let fix lind
              {es : list (E.e tags_t)}
              {ts : list E.t}
              (HR : Forall2 (fun e τ => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es ts)
          : Forall2 (P errs Γ) es ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Htail
            => Forall2_cons _ _ (chind _ _ _ _ Hh) (lind Htail)
          end in
      let fix lind_stk
              {es : list (E.e tags_t)} {τ : E.t}
              (HRs : Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es)
          : Forall (fun e => P errs Γ e τ) es :=
          match HRs with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hhead Htail
            => Forall_cons _ (chind _ _ _ _ Hhead) (lind_stk Htail)
          end in
      let fix fields_ind
              {efs : F.fs string (E.t * E.e tags_t)}
              {tfs : F.fs string E.t}
              (HRs : F.relfs
                       (fun te τ =>
                          (fst te) = τ /\
                          let e := snd te in
                          ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs)
          : F.relfs
              (fun te τ => let e := snd te in P errs Γ e τ)
              efs tfs :=
          match HRs with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons te τ (conj HName (conj _ Hhead)) Htail
            => Forall2_cons te τ
                           (conj HName (chind errs Γ _ _ Hhead))
                           (fields_ind Htail)
          end in
      match HY with
      | chk_bool _ _ b i     => HBool errs Γ b i
      | chk_bit _ _ _ _ H i => HBit _ _ _ _ H i
      | chk_int _ _ _ _ H i => HInt _ _ _ _ H i
      | chk_var _ _ _ _ i HP HV => HVar _ _ _ _ i HP HV
      | chk_slice _ _ _ _ _ _ _ i Hlohiw Ht He
        => HSlice _ _ _ _ _ _ _ i Hlohiw Ht He (chind _ _ _ _ He)
      | chk_cast _ _ _ _ _ i HPC He
        => HCast _ _ _ _ _ i HPC He (chind _ _ _ _ He)
      | chk_uop _ _ _ _ _ _ i Huop He
        => HUop _ _ _ _ _ _ i Huop He (chind _ _ _ _ He)
      | chk_bop _ _ _ _ _ _ _ _ i Hbop He1 He2
        => HBop _ _ _ _ _ _ _ _ i Hbop
               He1 (chind _ _ _ _ He1)
               He2 (chind _ _ _ _ He2)
      | chk_mem _ _ _ _ _ _ _ _ i Hget He
        => HMem _ _ _ _ _ _ _ _ i Hget He (chind _ _ _ _ He)
      | chk_error _ _ _ i HOK => HError errs Γ _ i HOK
      | chk_matchkind _ _ mk i  => HMatchKind errs Γ mk i
      | chk_tuple _ _ _ i _ HR => HTuple _ _ _ i _ HR (lind HR)
      | chk_struct_lit _ _ _ _ i HRs
        => HStructLit _ _ _ _ i HRs (fields_ind HRs)
      | chk_hdr_lit _ _ _ _ i _ HP HRs Hb
        => HHdrLit _ _ _ _ i _ HP
                  HRs (fields_ind HRs)
                  Hb (chind _ _ _ _ Hb)
      | chk_stack _ _ _ _ _ _ i Hn Hni Hlen HP HRs
        => HStack _ _ _ _ _ _ i Hn Hni Hlen HP HRs (lind_stk HRs)
      | chk_access _ _ _ _ i _ _ Hidx He
        => HAccess _ _ _ _ i _ _ Hidx He (chind _ _ _ _ He)
      end.
  (**[]*)
End CheckExprInduction.

Section PatternCheckInduction.
  Variable P : PR.pat -> E.t -> Prop.
  
  Hypothesis HWild : forall t, P [{ ?? }] t.
  
  Hypothesis HMask : forall p1 p2 w,
      check_pat p1 {{ bit<w> }} ->
      P p1 {{ bit<w> }} ->
      check_pat p2 {{ bit<w> }} ->
      P p2 {{ bit<w> }} ->
      P [{ p1 &&& p2 }] {{ bit<w> }}.
  
  Hypothesis HRange : forall p1 p2 w,
      check_pat p1 {{ bit<w> }} ->
      P p1 {{ bit<w> }} ->
      check_pat p2 {{ bit<w> }} ->
      P p2 {{ bit<w> }} ->
      P [{ p1 .. p2 }] {{ bit<w> }}.
  
  Hypothesis HBit : forall w n, P [{ w PW n }] {{ bit<w> }}.
  
  Hypothesis HInt : forall w z, P [{ w PS z }] {{ int<w> }}.
  
  Hypothesis HTuple : forall ps ts,
      Forall2 check_pat ps ts ->
      Forall2 P ps ts ->
      P [{ PTUP ps }] {{ tuple ts }}.
  
  Definition custom_check_pat_ind : forall p t,
      check_pat p t -> P p t :=
    fix pind p t (H : check_pat p t) :=
      let fix lind {ps : list PR.pat} {ts : list E.t}
              (H : Forall2 check_pat ps ts) : Forall2 P ps ts :=
          match H with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht
            => Forall2_cons _ _ (pind _ _ Hh) (lind Ht)
          end in
      match H with
      | chk_wild _ => HWild _
      | chk_mask _ _ _ Hp1 Hp2
        => HMask _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | chk_range _ _ _ Hp1 Hp2
        => HRange _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | chk_pbit w n => HBit w n
      | chk_pint w z => HInt w z
      | chk_ptup _ _ H => HTuple _ _ H (lind H)
      end.
  (**[]*)
End PatternCheckInduction.

(** A custom induction principle for parser-expression typing. *)
Section CheckParserExprInduction.
  Variable tags_t: Type.
  
  (** An arbitrary predicate. *)
  Variable P : user_states -> errors -> gamma -> PR.e tags_t -> Prop.
  
  Hypothesis HGoto : forall sts errs Γ st i,
      valid_state sts st ->
      P sts errs Γ p{ goto st @ i }p.
  
  Hypothesis HSelect : forall sts errs Γ e def cases i τ,
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⟅ sts, errs, Γ ⟆ ⊢ def ->
                   P sts errs Γ def ->
                   Forall
                     (fun pe =>
                        let p := fst pe in
                        let e := snd pe in
                        check_pat p τ /\ ⟅ sts, errs, Γ ⟆ ⊢ e) cases ->
                   F.predfs_data (P sts errs Γ) cases ->
                   P sts errs Γ p{ select e { cases } default:=def @ i }p.
  
  (** Custom induction principle.
      Do [induction ?H using custom_check_prsrexpr_ind] *)
  Definition custom_check_prsrexpr_ind :
    forall (sts : user_states) (errs : errors) (Γ : gamma) (e : PR.e tags_t)
      (Hy : ⟅ sts, errs, Γ ⟆ ⊢ e), P sts errs Γ e :=
    fix chind sts errs Γ e Hy :=
      let fix lind
              {cases : F.fs PR.pat (PR.e tags_t)} {τ : E.t}
              (HR : Forall
                      (fun pe =>
                         let p := fst pe in
                         let e := snd pe in
                         check_pat p τ /\ ⟅ sts, errs, Γ ⟆ ⊢ e) cases)
          : F.predfs_data (P sts errs Γ) cases :=
          match HR with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ (conj _ He) Htail
            => Forall_cons _ (chind _ _ _ _ He) (lind Htail)
          end in
      match Hy with
      | chk_goto _ _ _ _ Hst i => HGoto _ _ _ _ Hst i
      | chk_select _ _ _ _ _ _ i _
                   He Hd Hcases
        => HSelect _ _ _ _ _ _ i _ He Hd
                  (chind _ _ _ _ Hd) Hcases (lind Hcases)
      end.
  (**[]*)
End CheckParserExprInduction.
