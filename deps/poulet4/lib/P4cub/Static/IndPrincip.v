Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Static.Util
        Poulet4.P4cub.Static.Typing.
Import P.P4cubNotations Env.EnvNotations.

(** Custom induction principle for ok types. *)
Section OkBoomerInduction.
  Variable P : Delta -> E.t -> Prop.
  Variable Δ : Delta.

  Hypothesis HBool : P Δ {{ Bool }}.
  Hypothesis HBit : forall w, P Δ {{ bit<w> }}.
  Hypothesis HInt : forall w, P Δ {{ int<w> }}.
  Hypothesis HError : P Δ {{ error }}.
  Hypothesis HMatchkind : P Δ {{ matchkind }}.
  Hypothesis HTuple : forall ts,
      Forall (t_ok Δ) ts ->
      Forall (P Δ) ts ->
      P Δ {{ tuple ts }}.
  Hypothesis HStruct : forall ts,
      F.predfs_data (t_ok Δ) ts ->
      F.predfs_data (P Δ) ts ->
      P Δ {{ struct { ts } }}.
  Hypothesis HHeader : forall ts,
      F.predfs_data (t_ok Δ) ts ->
      F.predfs_data (P Δ) ts ->
      P Δ {{ hdr { ts } }}.
  Hypothesis HStack : forall ts n,
      F.predfs_data (t_ok Δ) ts ->
      F.predfs_data (P Δ) ts ->
      P Δ {{ stack ts[n] }}.
  Hypothesis HVar : forall T,
      In T Δ -> P Δ T.

  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_t_ok        _ind]. *)       
  Definition custom_t_ok_ind :
    forall (τ : E.t) (HY : t_ok Δ τ), P Δ τ :=
    fix toind τ HY :=
      let fix lind {ts : list E.t} (Hts : Forall (t_ok Δ) ts)
          : Forall (P Δ) ts :=
          match Hts with
          | Forall_nil _         => Forall_nil _
          | Forall_cons _ Pt Pts => Forall_cons _ (toind _ Pt) (lind Pts)
          end in
      let fix find {ts : F.fs string E.t} (Hts : F.predfs_data (t_ok Δ) ts)
          : F.predfs_data (P Δ) ts :=
          match Hts with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Pt Pts => Forall_cons _ (toind _ Pt) (find Pts)
          end in
      match HY with
      | bool_ok _          => HBool
      | bit_ok _ w         => HBit w
      | int_ok _ w         => HInt w
      | error_ok _         => HError
      | matchkind_ok _     => HMatchkind
      | tuple_ok _ _ Hts   => HTuple _ Hts (lind Hts)
      | struct_ok _ _ Hts  => HStruct _ Hts (find Hts)
      | header_ok _ _ Hts  => HHeader _ Hts (find Hts)
      | stack_ok _ _ n Hts => HStack _ n Hts (find Hts)
      | var_ok _ T HT      => HVar _ HT
      end.
End OkBoomerInduction.

(** Custom induction principle for expression typing. *)
Section CheckExprInduction.
  Variable (tags_t : Type).
  
  (** An arbitrary predicate. *)
  Variable P : Delta -> Gamma -> E.e tags_t -> E.t -> Prop.
  
  Hypothesis HBool : forall Δ Γ b i,
      P Δ Γ <{ BOOL b @ i }> {{ Bool }}.
  (**[]*)
  
  Hypothesis HBit : forall Δ Γ w n i,
      BitArith.bound w n ->
      P Δ Γ <{ w W n @ i }> {{ bit<w> }}.
  (**[]*)
  
  Hypothesis HInt : forall Δ Γ w z i,
      IntArith.bound w z ->
      P Δ Γ <{ w S z @ i }> {{ int<w> }}.
  (**[]*)
  
  Hypothesis HVar : forall Δ Γ x τ i,
      Env.find x Γ = Some τ ->
      t_ok Δ τ ->
      PT.proper_nesting τ ->
      P Δ Γ <{ Var x:τ @ i }> τ.
  (**[]*)
  
  Hypothesis HSlice : forall Δ Γ e τ hi lo w i,
      (lo <= hi < w)%positive ->
      numeric_width w τ ->
      ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
      P Δ Γ e τ ->
      let w' := (hi - lo + 1)%positive in
      P Δ Γ <{ Slice e:τ [hi:lo] @ i }> {{ bit<w'> }}.
  (**[]*)
  
  Hypothesis HCast : forall Δ Γ τ τ' e i,
      proper_cast τ' τ ->
      t_ok Δ τ' ->
      t_ok Δ τ ->
      ⟦ Δ, Γ ⟧ ⊢ e ∈ τ' ->
      P Δ Γ e τ' ->
      P Δ Γ <{ Cast e:τ @ i }> τ.
  (**[]*)
  
  Hypothesis HUop : forall Δ Γ op τ τ' e i,
      uop_type op τ τ' ->
      ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
      P Δ Γ e τ ->
      P Δ Γ <{ UOP op e:τ @ i }> τ'.
  
  Hypothesis HBop : forall Δ Γ op τ1 τ2 τ e1 e2 i,
      bop_type op τ1 τ2 τ ->
      ⟦ Δ , Γ ⟧ ⊢ e1 ∈ τ1 ->
      P Δ Γ e1 τ1 ->
      ⟦ Δ , Γ ⟧ ⊢ e2 ∈ τ2 ->
      P Δ Γ e2 τ2 ->
      P Δ Γ <{ BOP e1:τ1 op e2:τ2 @ i }> τ.
  
  Hypothesis HMem : forall Δ Γ e x fs τ τ' i,
      F.get x fs = Some τ' ->
      member_type fs τ ->
      t_ok Δ τ ->
      t_ok Δ τ' ->
      ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
      P Δ Γ e τ ->
      P Δ Γ <{ Mem e:τ dot x @ i }> τ'.
  (**[]*)
  
  Hypothesis HTuple : forall Δ Γ es i ts,
      Forall2 (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ) es ts ->
      Forall2 (P Δ Γ) es ts ->
      P Δ Γ <{ tup es @ i }> {{ tuple ts }}.
  (**[]*)
  
  Hypothesis HStructLit : forall Δ Γ efs tfs i,
      F.relfs
        (fun te τ =>
           (fst te) = τ /\ t_ok Δ τ /\
           let e := snd te in
           ⟦ Δ , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      F.relfs
        (fun te τ => let e := snd te in P Δ Γ e τ)
        efs tfs ->
      P Δ Γ <{ struct { efs } @ i }> {{ struct { tfs } }}.
  (**[]*)
  
  Hypothesis HHdrLit : forall Δ Γ efs tfs i b,
      PT.proper_nesting {{ hdr { tfs } }} ->
      F.relfs
        (fun te τ =>
           (fst te) = τ /\ t_ok Δ τ /\
           let e := snd te in
           ⟦ Δ , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      F.relfs
        (fun te τ => let e := snd te in P Δ Γ e τ)
        efs tfs ->
      ⟦ Δ, Γ ⟧ ⊢ b ∈ Bool ->
      P Δ Γ b {{ Bool }} ->
      P Δ Γ <{ hdr { efs } valid:=b @ i }> {{ hdr { tfs } }}.
  (**[]*)
  
  Hypothesis HError : forall Δ Γ err i,
      P Δ Γ <{ Error err @ i }> {{ error }}.
  (**[]*)
  
  Hypothesis HMatchKind : forall Δ Γ mkd i,
      P Δ Γ <{ Matchkind mkd @ i }> {{ matchkind }}.
  (**[]*)
  
  Hypothesis HStack : forall Δ Γ ts hs n ni i,
      BitArith.bound 32%positive (Zpos n) ->
      (0 <= ni < (Zpos n))%Z ->
      Pos.to_nat n = length hs ->
      PT.proper_nesting {{ stack ts[n] }} ->
      t_ok Δ {{ stack ts[n] }} ->
      Forall (fun e => ⟦ Δ, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
      Forall (fun e => P Δ Γ e {{ hdr { ts } }}) hs ->
      P Δ Γ <{ Stack hs:ts[n] nextIndex:=ni @ i }> {{ stack ts[n] }}.
  (**[]*)
  
  Hypothesis HAccess : forall Δ Γ e idx i ts n,
      (0 <= idx < (Zpos n))%Z ->
      t_ok Δ {{ stack ts[n] }} ->
      ⟦ Δ, Γ ⟧ ⊢ e ∈ stack ts[n] ->
      P Δ Γ e {{ stack ts[n] }} ->
      P Δ Γ <{ Access e[idx] @ i }> {{ hdr { ts } }}.
  (**[]*)
  
  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_check_expr_ind]. *)
  Definition custom_check_expr_ind :
    forall (Δ : Delta) (Γ : Gamma) (e : E.e tags_t) (τ : E.t)
      (HY : ⟦ Δ, Γ ⟧ ⊢ e ∈ τ), P Δ Γ e τ :=
    fix chind Δ Γ e τ HY :=
      let fix lind
              {es : list (E.e tags_t)}
              {ts : list E.t}
              (HR : Forall2 (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ) es ts)
          : Forall2 (P Δ Γ) es ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Htail
            => Forall2_cons _ _ (chind _ _ _ _ Hh) (lind Htail)
          end in
      let fix lind_stk
              {es : list (E.e tags_t)} {τ : E.t}
              (HRs : Forall (fun e => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ) es)
          : Forall (fun e => P Δ Γ e τ) es :=
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
                          (fst te) = τ /\ t_ok Δ τ /\
                          let e := snd te in
                          ⟦ Δ , Γ ⟧ ⊢ e ∈ τ) efs tfs)
          : F.relfs
              (fun te τ => let e := snd te in P Δ Γ e τ)
              efs tfs :=
          match HRs with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons te τ (conj HName (conj _ (conj _ Hhead))) Htail
            => Forall2_cons te τ
                           (conj HName (chind Δ Γ _ _ Hhead))
                           (fields_ind Htail)
          end in
      match HY with
      | chk_bool _ _ b i     => HBool Δ Γ b i
      | chk_bit _ _ _ _ H i => HBit _ _ _ _ H i
      | chk_int _ _ _ _ H i => HInt _ _ _ _ H i
      | chk_var _ _ _ _ i HP Hok HV => HVar _ _ _ _ i HP Hok HV
      | chk_slice _ _ _ _ _ _ _ i Hlohiw Ht He
        => HSlice _ _ _ _ _ _ _ i Hlohiw Ht He (chind _ _ _ _ He)
      | chk_cast _ _ _ _ _ i HPC Hok Hok' He
        => HCast _ _ _ _ _ i HPC Hok Hok' He (chind _ _ _ _ He)
      | chk_uop _ _ _ _ _ _ i Huop He
        => HUop _ _ _ _ _ _ i Huop He (chind _ _ _ _ He)
      | chk_bop _ _ _ _ _ _ _ _ i Hbop He1 He2
        => HBop _ _ _ _ _ _ _ _ i Hbop
               He1 (chind _ _ _ _ He1)
               He2 (chind _ _ _ _ He2)
      | chk_mem _ _ _ _ _ _ _ _ i Hok Hok' Hget He
        => HMem _ _ _ _ _ _ _ _ i Hok Hok' Hget He (chind _ _ _ _ He)
      | chk_error _ _ err i => HError Δ Γ err i
      | chk_matchkind _ _ mk i  => HMatchKind Δ Γ mk i
      | chk_tuple _ _ _ i _ HR => HTuple _ _ _ i _ HR (lind HR)
      | chk_struct_lit _ _ _ _ i HRs
        => HStructLit _ _ _ _ i HRs (fields_ind HRs)
      | chk_hdr_lit _ _ _ _ i _ HP HRs Hb
        => HHdrLit _ _ _ _ i _ HP
                  HRs (fields_ind HRs)
                  Hb (chind _ _ _ _ Hb)
      | chk_stack _ _ _ _ _ _ i Hn Hni Hlen HP Hok HRs
        => HStack _ _ _ _ _ _ i Hn Hni Hlen HP Hok HRs (lind_stk HRs)
      | chk_access _ _ _ _ i _ _ Hok Hidx He
        => HAccess _ _ _ _ i _ _ Hok Hidx He (chind _ _ _ _ He)
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
  Variable P : user_states -> Delta -> Gamma -> PR.e tags_t -> Prop.
  
  Hypothesis HGoto : forall sts Δ Γ st i,
      valid_state sts st ->
      P sts Δ Γ p{ goto st @ i }p.
  
  Hypothesis HSelect : forall sts Δ Γ e def cases i τ,
      ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
      ⟅ sts, Δ, Γ ⟆ ⊢ def ->
                P sts Δ Γ def ->
                Forall
                  (fun pe =>
                     let p := fst pe in
                     let e := snd pe in
                     check_pat p τ /\ ⟅ sts, Δ, Γ ⟆ ⊢ e) cases ->
                F.predfs_data (P sts Δ Γ) cases ->
                P sts Δ Γ p{ select e { cases } default:=def @ i }p.
  
  (** Custom induction principle.
      Do [induction ?H using custom_check_prsrexpr_ind] *)
  Definition custom_check_prsrexpr_ind :
    forall (sts : user_states) (Δ : Delta) (Γ : Gamma) (e : PR.e tags_t)
      (Hy : ⟅ sts, Δ, Γ ⟆ ⊢ e), P sts Δ Γ e :=
    fix chind sts Δ Γ e Hy :=
      let fix lind
              {cases : F.fs PR.pat (PR.e tags_t)} {τ : E.t}
              (HR : Forall
                      (fun pe =>
                         let p := fst pe in
                         let e := snd pe in
                         check_pat p τ /\ ⟅ sts, Δ, Γ ⟆ ⊢ e) cases)
          : F.predfs_data (P sts Δ Γ) cases :=
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
