Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.Static.Util
        Poulet4.P4cub.BigStep.Value.IndPrincip
        Poulet4.P4cub.BigStep.Value.Auxilary
        Coq.PArith.BinPos Coq.ZArith.BinInt
        Coq.micromega.Lia.
Import ProperType Val ValueNotations
       LValueNotations AllCubNotations
       Env.EnvNotations.

Reserved Notation "∇ ⊢ v ∈ τ"
         (at level 40, v custom p4value, τ custom p4type).

Reserved Notation "'LL' Δ , Γ ⊢ lval ∈ τ"
         (at level 40, Δ custom p4env, Γ custom p4env,
          lval custom p4lvalue, τ custom p4type).

Inductive type_value : v -> Expr.t -> Prop :=
| typ_bool (b : bool) :
    ∇ ⊢ VBOOL b ∈ Bool
| typ_bit (w : positive) (n : Z) :
    BitArith.bound w n ->
    ∇ ⊢ w VW n ∈ bit<w>
| typ_int (w : positive) (z : Z) :
    IntArith.bound w z ->
    ∇ ⊢ w VS z ∈ int<w>
| typ_tuple (vs : list v)
            (ts : list Expr.t) :
    Forall2 (fun v τ => ∇ ⊢ v ∈ τ) vs ts ->
    ∇ ⊢ TUPLE vs ∈ tuple ts
| typ_struct (vs : Field.fs string v)
             (ts : Field.fs string Expr.t) :
    Field.relfs (fun vl τ => ∇ ⊢ vl ∈ τ) vs ts ->
    ∇ ⊢ STRUCT { vs } ∈ struct { ts }
| typ_hdr (vs : Field.fs string v) (b : bool)
          (ts : Field.fs string Expr.t) :
    proper_nesting {{ hdr { ts } }} ->
    Field.relfs (fun vl τ => ∇ ⊢ vl ∈ τ) vs ts ->
    ∇ ⊢ HDR { vs } VALID:=b ∈ hdr { ts }
| typ_error (err : option string) :
    ∇ ⊢ ERROR err ∈ error
| typ_matchkind (mk : Expr.matchkind) :
    ∇ ⊢ MATCHKIND mk ∈ matchkind
| typ_headerstack (ts : Field.fs string Expr.t)
                  (hs : list (bool * Field.fs string v)) (ni : Z) :
    let n := Pos.of_nat (length hs) in
    BitArith.bound 32%positive (Zpos n) ->
    (0 <= ni < (Zpos n))%Z ->
    proper_nesting {{ stack ts[n] }} ->
    (* t_ok Δ {{ stack ts[n] }} -> *)
    Forall
      (fun bvs =>
         let b := fst bvs in
         let vs := snd bvs in
         ∇ ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
    ∇ ⊢ STACK hs:ts NEXT:=ni ∈ stack ts[n]
where "∇ ⊢ vl ∈ τ" := (type_value vl τ) : type_scope.

(** Custom induction for value typing. *)
Section ValueTypingInduction.
  (** Arbitrary predicate. *)
  Variable P : v -> Expr.t -> Prop.
  
  Hypothesis HBool : forall b, P ~{ VBOOL b }~ {{ Bool }}.
  
  Hypothesis HBit : forall w n,
      BitArith.bound w n ->
      P ~{ w VW n }~ {{ bit<w> }}.
  
  Hypothesis HInt : forall w z,
      IntArith.bound w z ->
      P ~{ w VS z }~ {{ int<w> }}.
  
  Hypothesis HMatchkind : forall mk, P ~{ MATCHKIND mk }~ {{ matchkind }}.

  Hypothesis HError : forall err,
      P ~{ ERROR err }~ {{ error }}.
  
  Hypothesis HTuple : forall  vs ts,
      Forall2 (fun v τ => ∇  ⊢ v ∈ τ) vs ts ->
      Forall2 P vs ts ->
      P ~{ TUPLE vs }~ {{ tuple ts }}.
  
  Hypothesis HStruct : forall  vs ts,
      Field.relfs (fun vl τ => ∇  ⊢ vl ∈ τ) vs ts ->
      Field.relfs (fun vl τ => P  vl τ) vs ts ->
      P  ~{ STRUCT { vs } }~ {{ struct { ts } }}.
  
  Hypothesis HHeader : forall  vs b ts,
      proper_nesting {{ hdr { ts } }} ->
      Field.relfs (fun vl τ => ∇  ⊢ vl ∈ τ) vs ts ->
      Field.relfs (fun vl τ => P  vl τ) vs ts ->
      P  ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}.
  
  Hypothesis HStack : forall  ts hs ni,
      let n := Pos.of_nat (length hs) in
      BitArith.bound 32%positive (Zpos n) ->
      (0 <= ni < (Zpos n))%Z ->
      proper_nesting {{ stack ts[n] }} ->
      Forall
        (fun bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ∇  ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
      Forall
        (fun bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           P  ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs ->
      P  ~{ STACK hs:ts NEXT:=ni }~ {{ stack ts[n] }}.
  
  (** Custom induction principle.
      Do [induction ?H using custom_type_value_ind]. *)
  Definition custom_type_value_ind :
    forall (vl : v) (τ : Expr.t)
      (Hy : ∇  ⊢ vl ∈ τ), P  vl τ :=
    fix tvind  vl τ Hy :=
      let fix lind {vs : list v}
              {ts : list Expr.t}
              (HR : Forall2 (fun v τ => ∇  ⊢ v ∈ τ) vs ts)
          : Forall2 (P ) vs ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht => Forall2_cons
                                       _ _
                                       (tvind _ _ Hh)
                                       (lind Ht)
          end in
      let fix fsind {vs : Field.fs string v}
              {ts : Field.fs string Expr.t}
              (HR : Field.relfs (fun vl τ => ∇  ⊢ vl ∈ τ) vs ts)
          : Field.relfs (fun vl τ => P  vl τ) vs ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj Hname Hvt)
                         Htail => Forall2_cons
                                   _ _
                                   (conj Hname (tvind _ _ Hvt))
                                   (fsind Htail)
          end in
      let fix hsind {hs : list (bool * Field.fs string v)}
              {ts : Field.fs string Expr.t}
              (HR :
                 Forall
                   (fun bvs =>
                      let b := fst bvs in
                      let vs := snd bvs in
                      ∇  ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs)
          : Forall
              (fun bvs =>
                 let b := fst bvs in
                 let vs := snd bvs in
                 P  ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs :=
          match HR with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hhead Htail => Forall_cons
                                          _ (tvind _ _ Hhead)
                                          (hsind Htail)
          end in
      match Hy with
      | typ_bool b => HBool b
      | typ_bit _ _ H => HBit _ _ H
      | typ_int _ _ H => HInt _ _ H
      | typ_matchkind mk => HMatchkind mk
      | typ_error err => HError err
      | typ_tuple _ _ Hvs => HTuple _ _ Hvs (lind Hvs)
      | typ_struct _ _ Hfs => HStruct _ _ Hfs (fsind Hfs)
      | typ_hdr _ b _ HP Hfs => HHeader _ b _ HP Hfs (fsind Hfs)
      | typ_headerstack _ _ _ Hn Hni HP Hhs =>
        HStack _ _ _ Hn Hni HP Hhs (hsind Hhs)
      end.
End ValueTypingInduction.

Inductive type_lvalue (Δ : Delta) (Γ : Gamma) : lv -> Expr.t -> Prop :=
| typ_var (x : string) (τ : Expr.t) :
    Envn.Env.find x Γ = Some τ ->
    t_ok Δ τ ->
    LL Δ, Γ ⊢ VAR x ∈ τ
| typ_slice (lval : lv) (hi lo w : positive) (τ : Expr.t) :
    (lo <= hi < w)%positive ->
    numeric_width w τ ->
    LL Δ, Γ ⊢ lval ∈ τ ->
    let w' := (hi - lo + 1)%positive in
    LL Δ, Γ ⊢ SLICE lval [hi:lo] ∈ bit<w'>
| typ_member (lval : lv) (x : string) (τ τ' : Expr.t) (ts : F.fs string Expr.t) :
    F.get x ts = Some τ' ->
    member_type ts τ ->
    t_ok Δ τ ->
    t_ok Δ τ' ->
    LL Δ, Γ ⊢ lval ∈ τ ->
    LL Δ, Γ ⊢ lval DOT x ∈ τ'
| typ_access (lval : lv) (idx : Z)
             (n : positive) (ts : F.fs string Expr.t) :
    (0 <= idx < Zpos n)%Z ->
    t_ok Δ {{ stack ts[n] }} ->
    LL Δ, Γ ⊢ lval ∈ stack ts[n] ->
    LL Δ, Γ ⊢ ACCESS lval[idx] ∈ hdr { ts }
where "'LL' Δ , Γ ⊢ lval ∈ τ" := (type_lvalue Δ Γ lval τ).

Require Import Poulet4.P4cub.Static.Static.

Section Lemmas.
  Import F.FieldTactics.
  
  Local Hint Resolve BitArith.bound0 : core.
  Local Hint Resolve IntArith.bound0 : core.
  Local Hint Resolve proper_inside_header_nesting : core.
  Local Hint Constructors type_value : core.
  Local Hint Constructors proper_nesting : core.
  Hint Rewrite repeat_length.
  
  Fail Lemma vdefault_types :
    forall (τ : Expr.t),
      proper_nesting τ ->
      let val := vdefault τ in
      ∇  ⊢ val ∈ τ.
  (*Proof.
    intros  τ HPN; simpl.
    induction τ using custom_t_ind; simpl; constructor;
      try invert_proper_nesting;
      autorewrite with core; auto; try lia;
        try (ind_list_Forall; repeat inv_Forall_cons;
             constructor; intuition; assumption);
        try (apply repeat_Forall; unravel; constructor);
        try (ind_list_predfs; repeat invert_cons_predfs;
             constructor; try split; unravel;
             intuition; assumption); auto.
  Qed. *)

  Lemma approx_type_typing : forall  V T,
      ∇  ⊢ V ∈ T -> approx_type V = T.
  Proof.
    intros  V T H;
      induction H using custom_type_value_ind;
      unravel; auto.
    - f_equal; induction H; inv H0;
        unravel; subst; f_equal; auto.
    - f_equal; induction H; inv H0;
        repeat relf_destruct;
        unravel; subst; f_equal; auto.
    - clear H; f_equal;
        induction H0; inv H1;
          repeat relf_destruct;
          unravel; subst; f_equal; auto.
  Qed.
  
  Local Hint Constructors check_expr : core.
  Local Hint Resolve approx_type_typing : core.
  Local Hint Constructors proper_nesting : core.
  Hint Rewrite map_length : core. 
  
  Lemma expr_of_value_types {tags_t : Type} :
    forall  V T,
      ∇  ⊢ V ∈ T ->
      forall i : tags_t,
        let e := expr_of_value i V in
        ⟦ [] , ∅ ⟧ ⊢ e ∈ T.
  Proof.
    intros  V T Hvt;
      induction Hvt using custom_type_value_ind;
      intros i e; subst e; unravel in *; eauto. (*
    - constructor; induction H;
        inv H0; unravel in *; auto.
    - constructor.
      unfold F.relfs in *.
      induction H; inv H0;
        repeat relf_destruct; subst;
          unravel in *; intuition.
      constructor;
        unfold F.relf; unravel; eauto.
    - constructor; auto; clear H.
      unfold F.relfs in *.
      induction H0; inv H1;
        try predf_destruct;
        repeat relf_destruct; subst;
          unravel in *; intuition.
      constructor;
        unfold F.relf; unravel; eauto.
    - constructor;
        autorewrite with core; auto.
      clear n ni H H0 H1 H2.
      ind_list_Forall; unravel;
        repeat inv_Forall_cons; auto.
      destruct a; constructor; auto. *)
  Admitted.
End Lemmas.
