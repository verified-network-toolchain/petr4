Require Import Poulet4.P4cub.BigStep.Value
        Poulet4.P4cub.Static.StaticUtil
        Poulet4.P4cub.BigStep.ValueIndPrincip
        Poulet4.P4cub.Syntax.SynAuxilary
        Poulet4.P4cub.BigStep.ValueAux
        Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.SynIndPrincip
        Coq.micromega.Lia.
Import ProperType Val ValueNotations
       LValueNotations P.P4cubNotations.

Reserved Notation "∇ errs ⊢ v ∈ τ"
         (at level 40, v custom p4value, τ custom p4type).

Reserved Notation "'LL' Γ ⊢ lval ∈ τ"
         (at level 40, lval custom p4lvalue, τ custom p4type).

Inductive type_value (errs : errors) : v -> E.t -> Prop :=
| typ_bool (b : bool) : ∇ errs ⊢ VBOOL b ∈ Bool
| typ_bit (w : positive) (n : Z) :
    BitArith.bound w n ->
    ∇ errs ⊢ w VW n ∈ bit<w>
| typ_int (w : positive) (z : Z) :
    IntArith.bound w z ->
    ∇ errs ⊢ w VS z ∈ int<w>
| typ_tuple (vs : list v)
            (ts : list E.t) :
    Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts ->
    ∇ errs ⊢ TUPLE vs ∈ tuple ts
| typ_struct (vs : Field.fs string v)
             (ts : Field.fs string E.t) :
    Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
    ∇ errs ⊢ STRUCT { vs } ∈ struct { ts }
| typ_hdr (vs : Field.fs string v) (b : bool)
          (ts : Field.fs string E.t) :
    proper_nesting {{ hdr { ts } }} ->
    Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
    ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }
| typ_error (err : option string) :
    match err with
    | None => True
    | Some err => Envn.Env.find err errs = Some tt
    end ->
    ∇ errs ⊢ ERROR err ∈ error
| typ_matchkind (mk : E.matchkind) :
    ∇ errs ⊢ MATCHKIND mk ∈ matchkind
| typ_headerstack (ts : Field.fs string E.t)
                  (hs : list (bool * Field.fs string v))
                  (n : positive) (ni : Z) :
    BitArith.bound 32%positive (Zpos n) ->
    (0 <= ni < (Zpos n))%Z ->
    Pos.to_nat n = length hs ->
    proper_nesting {{ stack ts[n] }} ->
    Forall
      (fun bvs =>
         let b := fst bvs in
         let vs := snd bvs in
         ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
    ∇ errs ⊢ STACK hs:ts[n] NEXT:=ni ∈ stack ts[n]
where "∇ errs ⊢ vl ∈ τ" := (type_value errs vl τ) : type_scope.

(** Custom induction for value typing. *)
Section ValueTypingInduction.
  (** Arbitrary predicate. *)
  Variable P : errors -> v -> E.t -> Prop.
  
  Hypothesis HBool : forall errs b, P errs ~{ VBOOL b }~ {{ Bool }}.
  
  Hypothesis HBit : forall errs w n,
      BitArith.bound w n ->
      P errs ~{ w VW n }~ {{ bit<w> }}.
  
  Hypothesis HInt : forall errs w z,
      IntArith.bound w z ->
      P errs ~{ w VS z }~ {{ int<w> }}.
  
  Hypothesis HMatchkind : forall errs mk, P errs ~{ MATCHKIND mk }~ {{ matchkind }}.

  Hypothesis HError : forall errs err,
      match err with
      | None => True
      | Some err => Envn.Env.find err errs = Some tt
      end ->
      P errs ~{ ERROR err }~ {{ error }}.
  
  Hypothesis HTuple : forall errs vs ts,
      Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts ->
      Forall2 (P errs) vs ts ->
      P errs ~{ TUPLE vs }~ {{ tuple ts }}.
  
  Hypothesis HStruct : forall errs vs ts,
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      Field.relfs (fun vl τ => P errs vl τ) vs ts ->
      P errs ~{ STRUCT { vs } }~ {{ struct { ts } }}.
  
  Hypothesis HHeader : forall errs vs b ts,
      proper_nesting {{ hdr { ts } }} ->
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      Field.relfs (fun vl τ => P errs vl τ) vs ts ->
      P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}.
  
  Hypothesis HStack : forall errs ts hs n ni,
      BitArith.bound 32%positive (Zpos n) ->
      (0 <= ni < (Zpos n))%Z ->
      Pos.to_nat n = length hs ->
      proper_nesting {{ stack ts[n] }} ->
      Forall
        (fun bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
      Forall
        (fun bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs ->
      P errs ~{ STACK hs:ts[n] NEXT:=ni }~ {{ stack ts[n] }}.
  
  (** Custom induction principle.
      Do [induction ?H using custom_type_value_ind]. *)
  Definition custom_type_value_ind :
    forall (errs : errors) (vl : v) (τ : E.t)
      (Hy : ∇ errs ⊢ vl ∈ τ), P errs vl τ :=
    fix tvind errs vl τ Hy :=
      let fix lind {vs : list v}
              {ts : list E.t}
              (HR : Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts)
          : Forall2 (P errs) vs ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht => Forall2_cons
                                       _ _
                                       (tvind _ _ _ Hh)
                                       (lind Ht)
          end in
      let fix fsind {vs : Field.fs string v}
              {ts : Field.fs string E.t}
              (HR : Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts)
          : Field.relfs (fun vl τ => P errs vl τ) vs ts :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj Hname Hvt)
                         Htail => Forall2_cons
                                   _ _
                                   (conj Hname (tvind _ _ _ Hvt))
                                   (fsind Htail)
          end in
      let fix hsind {hs : list (bool * Field.fs string v)}
              {ts : Field.fs string E.t}
              (HR :
                 Forall
                   (fun bvs =>
                      let b := fst bvs in
                      let vs := snd bvs in
                      ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs)
          : Forall
              (fun bvs =>
                 let b := fst bvs in
                 let vs := snd bvs in
                 P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs :=
          match HR with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hhead Htail => Forall_cons
                                          _ (tvind _ _ _ Hhead)
                                          (hsind Htail)
          end in
      match Hy with
      | typ_bool _ b => HBool _ b
      | typ_bit _ _ _ H => HBit _ _ _ H
      | typ_int _ _ _ H => HInt _ _ _ H
      | typ_matchkind _ mk => HMatchkind _ mk
      | typ_error _ _ Herr => HError _ _ Herr
      | typ_tuple _ _ _ Hvs => HTuple _ _ _ Hvs (lind Hvs)
      | typ_struct _ _ _ Hfs => HStruct _ _ _ Hfs (fsind Hfs)
      | typ_hdr _ _ b _ HP Hfs => HHeader _ _ b _ HP Hfs (fsind Hfs)
      | typ_headerstack _ _ _ _ _ Hn Hni Hlen HP
                        Hhs => HStack _ _ _ _ _ Hn Hni
                                     Hlen HP
                                     Hhs (hsind Hhs)
      end.
End ValueTypingInduction.

Inductive type_lvalue (Γ : gamma) : lv -> E.t -> Prop :=
| typ_var (x : string) (τ : E.t) :
    Envn.Env.find x Γ = Some τ ->
    LL Γ ⊢ VAR x ∈ τ
| typ_member (lval : lv) (x : string) (τ τ' : E.t) (ts : F.fs string E.t) :
    F.get x ts = Some τ' ->
    member_type ts τ ->
    LL Γ ⊢ lval ∈ τ ->
    LL Γ ⊢ lval DOT x ∈ τ'
| typ_access (lval : lv) (idx : Z)
             (n : positive) (ts : F.fs string E.t) :
    (0 <= idx < Zpos n)%Z ->
    LL Γ ⊢ lval ∈ stack ts[n] ->
    LL Γ ⊢ lval[idx] ∈ hdr { ts }
where "'LL' Γ ⊢ lval ∈ τ" := (type_lvalue Γ lval τ).

Import F.FieldTactics.

Local Hint Resolve BitArith.bound0 : core.
Local Hint Resolve IntArith.bound0 : core.
Local Hint Resolve proper_inside_header_nesting : core.
Local Hint Constructors type_value : core.
Local Hint Constructors proper_nesting : core.
Hint Rewrite repeat_length.

Lemma vdefault_types :
  forall (errs : errors) (τ : E.t),
    proper_nesting τ ->
    let val := vdefault τ in
    ∇ errs ⊢ val ∈ τ.
Proof.
  intros errs τ HPN; simpl.
  induction τ using custom_t_ind; simpl; constructor;
    try invert_proper_nesting;
    autorewrite with core; auto; try lia;
      try (ind_list_Forall; repeat inv_Forall_cons;
           constructor; intuition; assumption);
      try (apply repeat_Forall; unravel; constructor);
      try (ind_list_predfs; repeat invert_cons_predfs;
           constructor; try split; unravel;
           intuition; assumption); auto.
Qed.
