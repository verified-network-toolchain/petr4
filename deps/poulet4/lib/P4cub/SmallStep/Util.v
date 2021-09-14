Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.SmallStep.Value
        Poulet4.P4cub.Envn Poulet4.P4Arith
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Static.Static.

Section StepDefs.
  Import TypeEquivalence ProperType
         F.FieldTactics P4ArithTactics
         P.P4cubNotations Env.EnvNotations.
  
  Context {tags_t : Type}.
  
  (** Expression environment. *)
  Definition eenv : Type := Env.t (string) (E.e tags_t).
  
  (** Bit-slicing. *)
  Definition eval_slice (hi lo : positive) (v : E.e tags_t) : option (E.e tags_t) :=
    match v with
    | <{ _ W z @ i }>
    | <{ _ S z @ i }>
      => let w' := (hi - lo + 1)%positive in
        Some $ E.EBit (Npos w')
             (BitArith.mod_bound (Npos w') $
              BitArith.bitstring_slice z hi lo) i
    | _ => None
    end.
  (**[]*)
  
  Definition eval_cast
             (target : E.t) (v : E.e tags_t) : option (E.e tags_t) :=
    match target, v with
    | (E.TBit (Npos 1)), <{ TRUE @ i }>         => Some (E.EBit 1%N 1%Z i)
    | (E.TBit (Npos 1)), <{ FALSE @ i }>        => Some (E.EBit 1%N 0%Z i)
    | {{ Bool }}, E.EBit 1%N 1%Z i => Some <{ TRUE @ i }>
    | {{ Bool }}, E.EBit 1%N 0%Z i => Some <{ FALSE @ i }>
    | {{ bit<w> }}, E.EInt _ z i
      => let n := BitArith.mod_bound w z in
        Some <{ w W n @ i }>
    | {{ int<w> }}, <{ _ W n @ i }>
      => let z := IntArith.mod_bound w n in
        Some <{ w S z @ i }>
    | {{ bit<w> }}, <{ _ W n @ i }>
      => let n := BitArith.mod_bound w n in
        Some <{ w W n @ i }>
    | {{ int<w> }}, <{ _ S z @ i}>
      => let z := IntArith.mod_bound w z in
        Some <{ w S z @ i }>
    | {{ struct { fs } }}, <{ tup vs @ i }>
      => Some $ E.EStruct (combine (F.keys fs) $ combine (F.values fs) vs) i
    | {{ hdr { fs } }}, <{ tup vs @ i }>
      => Some
          $ E.EHeader
          (combine (F.keys fs) $ combine (F.values fs) vs) <{ TRUE @ i }> i
    | _, _ => None
    end.
  (**[]*)
  
  (** Default (value) Expression. *)
  Fixpoint edefault (i : tags_t) (τ : E.t) : E.e tags_t :=
    let fix lstruct (ts : list (E.t)) : list (E.e tags_t) :=
        match ts with
        | []     => []
        | τ :: ts => edefault i τ :: lstruct ts
        end in
    let fix fstruct (fs : F.fs string (E.t))
        : F.fs string (E.t * E.e tags_t) :=
        match fs with
        | [] => []
        | (x, τ) :: fs => (x, (τ, edefault i τ)) :: fstruct fs
        end in
    match τ with
    | {{ Bool }} => <{ BOOL false @ i }>
    | {{ bit<w> }} => E.EBit w 0%Z i
    | {{ int<w> }} => E.EInt w 0%Z i
    | {{ error }} => <{ Error None @ i }>
    | {{ matchkind }} => <{ Matchkind exact @ i }>
    | {{ tuple ts }} => E.ETuple (lstruct ts) i
    | {{ struct { fs } }} => E.EStruct (fstruct fs) i
    | {{ hdr { fs } }} => E.EHeader (fstruct fs) <{ BOOL false @ i }> i
    | {{ stack tfs[n] }}
      => let tefs := fstruct tfs in
        let hs :=
            repeat
            <{ hdr { tefs } valid:= BOOL false @ i @ i }>
            (Pos.to_nat n) in
        E.EHeaderStack tfs hs n 0%Z i
    end.
  (**[]*)
  
  (** Unary Operations. *)
  Definition eval_uop (op : E.uop) (e : E.e tags_t) : option (E.e tags_t) :=
    match op, e with
    | _{ ! }_, <{ BOOL b @ i }>
      => let b' := negb b in Some <{ BOOL b' @ i }>
    | _{ ~ }_, <{ w W n @ i }>
      => let n' := BitArith.bit_not w n in Some <{ w W n' @ i }>
    | _{ ~ }_, <{ w S n @ i }>
      => let n' := IntArith.bit_not w n in Some <{ w S n' @ i }>
    | _{ - }_, <{ w W z @ i }>
      => let z' := BitArith.neg w z in Some <{ w W z' @ i }>
    | _{ - }_, <{ w S z @ i }>
      => let z' := IntArith.neg w z in Some <{ w S z' @ i }>
    | _{ isValid }_, <{ hdr { _ } valid:=b @ i }> => Some b
    | _{ setValid }_, <{ hdr { fs } valid:=_ @ i }>
      => Some <{ hdr { fs } valid:=TRUE @ i @ i}>
    | _{ setInValid }_, <{ hdr { fs } valid:=b @ i }>
      => Some <{ hdr { fs } valid:=FALSE @ i @ i }>
    | _{ Size }_, <{ Stack _:_[size] nextIndex:=_ @ i }>
      => let w := 32%N in
        let s := Zpos size in Some <{ w W s @ i }>
    | _{ Next }_, <{ Stack hs:_[_] nextIndex:=ni @ _ }>
      => nth_error hs $ Z.to_nat ni
    | _{ Push p }_, <{ Stack hs:ts[n] nextIndex:=ni @ i }>
      => let pnat := Pos.to_nat p in
        let sizenat := Pos.to_nat n in
        let hdefault :=
            E.EHeader
              (F.map (fun τ => (τ, edefault i τ)) ts)
            <{ BOOL false @ i }> i in
        if lt_dec pnat sizenat then
          let new_hdrs := repeat hdefault pnat in
          let remains := firstn (sizenat - pnat) hs in
          Some $ E.EHeaderStack ts (new_hdrs ++ remains) n
               (Z.min (ni + Zpos p)%Z (Z.pos n - 1)%Z) i
        else
          let new_hdrs := repeat hdefault sizenat in
          Some $ E.EHeaderStack ts new_hdrs n (Z.pos n - 1)%Z i
    | _{ Pop p }_, <{ Stack hs:ts[n] nextIndex:=ni @ i }>
      => let pnat := Pos.to_nat p in
        let sizenat := Pos.to_nat n in
        let hdefault :=
            E.EHeader
              (F.map (fun τ => (τ, edefault i τ)) ts)
            <{ BOOL false @ i }> i in
        if lt_dec pnat sizenat then
          let new_hdrs := repeat hdefault pnat in
          let remains := skipn pnat hs in
          Some $ E.EHeaderStack ts (remains ++ new_hdrs) n
               (Z.max 0 (ni - Zpos p)%Z) i
        else
          let new_hdrs := repeat hdefault sizenat in
          Some $ E.EHeaderStack ts new_hdrs n 0%Z i
    | _, _ => None
    end.
  (**[]*)
  
  (** Binary operations. *)
  Definition eval_bop
             (op : E.bop) (v1 v2 : E.e tags_t) (i : tags_t) : option (E.e tags_t) :=
    match op, v1, v2 with
    | +{ + }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.plus_mod w n1 n2) i
    | +{ + }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.plus_mod w z1 z2) i
    | +{ |+| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.plus_sat w n1 n2) i
    | +{ |+| }+,  <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.plus_sat w z1 z2) i
    | +{ - }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.minus_mod w n1 n2) i
    | +{ - }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.minus_mod w z1 z2) i
    | +{ |-| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.minus_sat w n1 n2) i
    | +{ |-| }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.minus_sat w z1 z2) i
    | +{ × }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.mult_mod w n1 n2) i
    | +{ × }+, <{ w S n1 @ _ }>, <{ _ S n2 @ _ }>
      => Some $ E.EInt w (IntArith.mult_mod w n1 n2) i
    | +{ << }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.shift_left w n1 n2) i
    | +{ << }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
      => Some $ E.EInt w (IntArith.shift_left w z1 z2) i
    | +{ >> }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.shift_right w n1 n2) i
    | +{ >> }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
      => Some $ E.EInt w (IntArith.shift_right w z1 z2) i
    | +{ & }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.bit_and w n1 n2) i
    | +{ & }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.bit_and w z1 z2) i
    | +{ ^ }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.bit_xor w n1 n2) i
    | +{ ^ }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.bit_xor w z1 z2) i
    | +{ | }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ E.EBit w (BitArith.bit_or w n1 n2) i
    | +{ | }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ E.EInt w (IntArith.bit_or w z1 z2) i
    | +{ <= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n1 <=? n2)%Z i
    | +{ <= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z1 <=? z2)%Z i
    | +{ < }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n1 <? n2)%Z i
    | +{ < }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z1 <? z2)%Z i
    | +{ >= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n2 <=? n1)%Z i
    | +{ >= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z2 <=? z1)%Z i
    | +{ > }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n2 <? n1)%Z i
    | +{ > }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z2 <? z1)%Z i
    | +{ && }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ E.EBool (b1 && b2) i
    | +{ || }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ E.EBool (b1 || b2) i
    | +{ == }+, _, _ => Some $ E.EBool (ExprEquivalence.eqbe v1 v2) i
    | +{ != }+, _, _ => Some $ E.EBool (negb $ ExprEquivalence.eqbe v1 v2) i
    | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
      => Some $ E.EBit (w1 + w2)%N (BitArith.concat w1 w2 n1 n2) i
    | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 S n2 @ _ }>
      => Some $ E.EBit (w1 + Npos w2)%N (BitArith.concat w1 (Npos w2) n1 n2) i
    | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 S n2 @ _ }>
      => Some $ E.EInt (w1 + w2)%positive (IntArith.concat (Npos w1) (Npos w2) n1 n2) i
    | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 W n2 @ _ }>
      =>
      match w2 with
      | 0%N => 
        Some (E.EInt w1 n1 i)
      | Npos w2 =>
        Some $ E.EInt (w1 + w2)%positive (IntArith.concat (Npos w1) (Npos w2) n1 n2) i
      end
    | _, _, _ => None
    end.
  (**[]*)
  
  (** Get header stack data from value. *)
  Definition header_stack_data (v : E.e tags_t)
    : option (positive * Z *
              F.fs string (E.t) *
              (list (E.e tags_t))) :=
    match v with
    | <{ Stack hs:ts[n] nextIndex:=ni @ _}> => Some (n,ni,ts,hs)
    | _ => None
    end.
  (**[]*)
  
  Definition eval_member (x : string) (v : E.e tags_t) : option (E.e tags_t) :=
    match v with
    | <{ struct { vs } @ _ }>
    | <{ hdr { vs } valid:=_ @ _ }> => vs ▷ F.get x >>| snd
    | _                             => None
    end.
  (**[]*)
  
  Section Edefault.
    Local Hint Constructors value : core.
    
    Lemma value_edefault : forall i τ, value (edefault i τ).
    Proof.
      induction τ using custom_t_ind; unravel; auto 1;
        try (constructor; apply repeat_Forall); constructor; auto 1;
          try (ind_list_predfs; unfold F.predfs_data in * );
          try ind_list_Forall; unravel in *; auto 4.
    Qed.
  End Edefault.
  
  Section HelpersType.
    Local Hint Constructors check_expr : core.
    Local Hint Extern 0 => bit_bounded : core.
    Local Hint Extern 0 => int_bounded : core.
    
    Import CanonicalForms.
    
    Lemma eval_slice_types : forall errs Γ v v' τ hi lo w,
        eval_slice hi lo v = Some v' ->
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        let w' := (Npos hi - Npos lo + 1)%N in
        ⟦ errs, Γ ⟧ ⊢ v' ∈ bit<w'>.
    Proof.
      intros errs Γ v v' τ hi lo w Heval Hv Hw Hnum Ht w'; subst w';
        inv Hnum; assert_canonical_forms; unravel in *; inv Heval; auto 2.
    Admitted.
    
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    
    Lemma eval_cast_types : forall errs Γ τ τ' v v',
        eval_cast τ' v = Some v' ->
        value v ->
        proper_cast τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
    Proof.
      intros errs Γ τ τ' v v' Heval Hv Hpc Ht;
        inv Hpc; assert_canonical_forms; unravel in *;
          try match goal with
              | H: context [ if ?b then _ else _ ]
                |- _ => destruct b eqn:?
              end; try (inv Heval; auto 2; assumption).
      - destruct x; try (inv Heval; auto 2; assumption).
        inv Heval; auto 2.
        constructor.
        unfold BitArith.bound.
        unfold BitArith.upper_bound.
        lia.
    Admitted.
    
        (*
      - destruct w; inv Heval; auto 2.
      - destruct w2; inv Heval; auto 2.
      - inv Heval. constructor.
        generalize dependent fs.
        ind_list_Forall; intros [| [? ?] ?] ?;
                                unravel in *; try inv_Forall2_cons;
          constructor; try split;
            unravel; try apply IHx; auto 2.
      - inv Heval; constructor; auto 1.
        + apply pn_header. rewrite F.predfs_data_map. assumption.
        + clear x0 H0. generalize dependent fs.
          ind_list_Forall; intros [| [? ?] ?] ? ;
            unravel in *; try inv_Forall2_cons;
              constructor; try split;
                unravel; try apply IHx; auto 2.
    Qed.
         *)
    
    Lemma eval_bop_types : forall Γ errs op τ1 τ2 τ (i : tags_t) v1 v2 v,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        eval_bop op v1 v2 i = Some v ->
        ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
    Proof.
      intros Γ errs op τ1 τ2 τ v1 v2 v i Hbop Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbop; unravel in *; try inv_numeric;
          repeat assert_canonical_forms;
          try (inv_numeric_width; assert_canonical_forms);
          try (inv Heval; auto 2; assumption).
    Qed.
    
    Lemma eval_member_types : forall errs Γ x v v' ts τ τ',
        eval_member x v = Some v' ->
        value v ->
        member_type ts τ ->
        F.get x ts = Some τ' ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
    Proof.
      intros errs Γ x v v' ts τ τ' Heval Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms.
      - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
            unravel in *; inv Heval; intuition.
      - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
            unravel in *; inv Heval; intuition.
    Qed.
    
    Local Hint Constructors proper_nesting : core.
    Hint Rewrite repeat_length.
    Local Hint Resolve proper_inside_header_nesting : core.
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    Local Hint Constructors error_ok : core.
    
    Lemma edefault_types : forall errs Γ i τ,
        PT.proper_nesting τ ->
        let e := edefault i τ in
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ.
    Proof.
      intros; subst e; induction τ using custom_t_ind; unravel;
        invert_proper_nesting; auto 2;
          constructor; autorewrite with core; auto 2;
            try (apply repeat_Forall; constructor; auto 2);
            try (ind_list_Forall; repeat inv_Forall_cons; constructor; intuition);
            try (ind_list_predfs; repeat invert_cons_predfs; constructor;
                 try split; unravel; intuition).
    Qed.
    
    Local Hint Resolve Forall_impl : core.
    Local Hint Resolve Forall_firstn : core.
    Local Hint Resolve Forall_skipn : core.
    Local Hint Resolve proper_inside_header_nesting : core.
    Local Hint Resolve edefault_types : core.
    Hint Rewrite app_length.
    Hint Rewrite Forall_app.
    Hint Rewrite firstn_length_le.
    Hint Rewrite skipn_length.
    Hint Rewrite map_length.
    Hint Rewrite (@F.predfs_data_map string).
    Hint Rewrite @F.map_fst.
    Hint Rewrite @map_compose.
    Hint Rewrite (@Forall2_map_l E.t).
    Hint Rewrite (@Forall2_Forall E.t).
    Hint Rewrite (@F.predfs_data_map).
    Hint Rewrite @F.relfs_split_map_iff.
    Hint Rewrite @F.map_snd.
    
    Lemma eval_uop_types : forall errs Γ op e v τ τ',
        uop_type op τ τ' -> value e -> eval_uop op e = Some v ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ'.
    Proof.
      intros errs Γ op e v τ τ' Huop Hev Heval Het;
        inv Huop; try inv_numeric;
          assert_canonical_forms; unravel in *;
            inv Heval; auto 2; invert_proper_nesting;
              repeat match goal with
                     | H: (if ?b then _ else _) = Some _
                       |- _ => destruct b as [? | ?] eqn:?
                     | H: Some _ = Some _ |- _ => inv H
                     end; eauto 2;
                try constructor; auto 2; try (destruct n; lia);
                  autorewrite with core; try lia;
                    try split; auto 2;
                      try (apply repeat_Forall; constructor; auto 2;
                           autorewrite with core in *; split; [intuition | unravel; eauto 5]).
      - eapply Forall_nth_error in H9; eauto 1; simpl in *; auto 1.
    Qed.
  End HelpersType.
  
  Section HelpersExist.
    Import CanonicalForms.
    
    Lemma eval_slice_exists : forall errs Γ v τ hi lo w,
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        exists v', eval_slice hi lo v = Some v'.
    Proof.
      intros errs Γ v τ hi lo w Hv Hw Hnum Ht;
        inv Hnum; assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_cast_exists : forall errs Γ e τ τ',
        value e ->
        proper_cast τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        exists v, eval_cast τ' e = Some v.
    Proof.
      intros ? ? ? ? ? Hv Hpc Het; inv Hpc; assert_canonical_forms;
        unravel; simpl in *; eauto 2.
      - destruct x; eauto 2.
      - destruct x; eauto 2; destruct p; eauto 2;
          try (cbv in H0; destruct H0; try destruct p; discriminate).
      - destruct w; eauto 2.
      - destruct w2; eauto 2.
    Admitted.
    
    Lemma eval_bop_exists : forall errs Γ op τ1 τ2 τ (i : tags_t) v1 v2,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 ->
        exists v, eval_bop op v1 v2 i = Some v.
    Proof.
      intros errs Γ op τ1 τ2 τ i v1 v2 Hbop Hv1 Hv2 Ht1 Ht2;
        inv Hbop; try inv_numeric; try inv_numeric_width;
          repeat assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_uop_exists : forall op errs Γ e τ τ',
        uop_type op τ τ' -> value e -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        exists v, eval_uop op e = Some v.
    Proof.
      intros op errs Γ e τ τ' Hu Hv Het; inv Hu;
        try inv_numeric; assert_canonical_forms;
          unravel; eauto 2.
      - assert (Hnihs : (Z.to_nat x0 < length x)%nat) by lia.
        pose proof nth_error_exists _ _ Hnihs as [? Hnth].
        rewrite Hnth; eauto 2.
      - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
      - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
    Qed.
    
    Lemma eval_member_exists : forall errs Γ x v ts τ τ',
        value v ->
        member_type ts τ ->
        F.get x ts = Some τ' ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        exists v', eval_member x v = Some v'.
    Proof.
      intros errs Γ x v ts τ τ' Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms; unravel.
      - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
      - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
    Qed.
  End HelpersExist.
  
  (** Lookup an lvalue. *)
  Fixpoint lv_lookup (ϵ : eenv) (lv : E.e tags_t) : option (E.e tags_t) :=
    match lv with
    | <{ Var x:_ @ _ }> => Env.find x ϵ
    | <{ Mem lv:_ dot x @ _ }> =>
      (* TODO: use monadic bind. *)
      match lv_lookup ϵ lv with
      | Some <{ struct { fs } @ _ }>
      | Some <{ hdr { fs } valid:=_  @ _ }> => fs ▷ F.get x >>| snd
      | _ => None
      end
    | <{ Access lv[n] @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ Stack vss:_[_] nextIndex:=_ @ _ }> => nth_error vss (Z.to_nat n)
      | _ => None
      end
    | _ => None
    end.
  (**[]*)
  
  (** Updating an lvalue in an environment. *)
  Fixpoint lv_update (lv v : E.e tags_t) (ϵ : eenv) : eenv :=
    match lv with
    | <{ Var x:_ @ _ }> => !{ x ↦ v ;; ϵ }!
    | <{ Mem lv:_ dot x @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ struct { vs } @ i }>
        => match F.get x vs with
          | None => ϵ
          | Some (τ,_) => lv_update lv (E.EStruct (F.update x (τ,v) vs) i) ϵ
          end
      | Some <{ hdr { vs } valid:=b @ i }>
        => match F.get x vs with
          | None => ϵ
          | Some (τ,_) => lv_update lv (E.EHeader (F.update x (τ,v) vs) b i) ϵ
          end
      | _ => ϵ
      end
    | <{ Access lv[n] @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ Stack vss:ts[size] nextIndex:=ni @ i }> =>
        let vss := nth_update (Z.to_nat n) v vss in
        lv_update lv <{ Stack vss:ts[size] nextIndex:=ni @ i }> ϵ
      | _ => ϵ
      end
    | _ => ϵ
    end.
  (**[]*)
  
  (** Create a new environment
      from a closure environment where
      values of [In] args are substituted
      into the function parameters. *)
  Definition copy_in
             (argsv : E.args tags_t)
             (ϵcall : eenv) : eenv -> eenv :=
    F.fold (fun x arg ϵ =>
              match arg with
              | P.PAIn (_,v)     => !{ x ↦ v ;; ϵ }!
              | P.PAInOut (_,lv) => match lv_lookup ϵcall lv with
                                   | None   => ϵ
                                   | Some v => !{ x ↦ v ;; ϵ }!
                                   end
              | P.PAOut _    => ϵ
              end) argsv.
  (**[]*)
  
  (** Update call-site environment with
      out variables from function call evaluation. *)
  Definition copy_out
             (argsv : E.args tags_t)
             (ϵf : eenv) : eenv -> eenv :=
    F.fold (fun x arg ϵ =>
              match arg with
              | P.PAIn _ => ϵ
              | P.PAOut (_,lv)
              | P.PAInOut (_,lv) =>
                match Env.find x ϵf with
                | None   => ϵ
                | Some v => lv_update lv v ϵ
                end
              end) argsv.
  (**[]*)
  
  (** Table environment. *)
  Definition tenv : Type := Env.t string (CD.table tags_t).
  
  (** Function declarations and closures. *)
  Inductive fdecl : Type :=
  | FDecl (closure : eenv) (fs : fenv) (ins : ienv) (body : ST.s tags_t)
  with fenv : Type :=
  | FEnv (fs : Env.t string fdecl)
  (** Action declarations and closures *)
  with adecl : Type :=
  | ADecl (closure : eenv) (fs : fenv) (ins : ienv) (aa : aenv) (body : ST.s tags_t)
  with aenv : Type :=
  | AEnv (aa : Env.t string adecl)
  (** Instances and Environment. *)
  with inst : Type :=
  | CInst (closure : eenv) (fs : fenv) (ins : ienv)
          (tbls : tenv) (aa : aenv)
          (apply_blk : ST.s tags_t)  (* control instance *)
  | PInst (* TODO: parser instance *)
  | EInst (* TODO: extern object instance *)
  with ienv : Type :=
  | IEnv (ins : Env.t string inst).
  (**[]*)
  
  (** Function lookup. *)
  Definition lookup '(FEnv fs : fenv) : string -> option fdecl := fun s => Env.find s fs.
  
  (** Bind a function declaration to an environment. *)
  Definition update '(FEnv fs : fenv) (x : string) (d : fdecl) : fenv :=
    FEnv !{ x ↦ d ;; fs }!.
  (**[]*)
  
  (** Instance lookup. *)
  Definition ilookup '(IEnv fs : ienv) : string -> option inst := fun i => Env.find i fs.
  
  (** Bind an instance to an environment. *)
  Definition iupdate '(IEnv fs : ienv) (x : string) (d : inst) : ienv :=
    IEnv !{ x ↦ d ;; fs }!.
  (**[]*)
  
  (** Action lookup. *)
  Definition alookup '(AEnv aa : aenv) : string -> option adecl := (fun x => Env.find x aa).
  
  (** Bind a function declaration to an environment. *)
  Definition aupdate '(AEnv aa : aenv) (x : string) (d : adecl) : aenv :=
    AEnv !{ x ↦ d ;; aa }!.
  (**[]*)
  
  (** Control plane table entries,
      essentially mapping tables to an action call. *)
  Definition entries : Type :=
    list (E.e tags_t * E.matchkind) ->
    list string ->
    string * E.args tags_t.
  (**[]*)
  
  (** Control plane configuration. *)
  Definition ctrl : Type := Env.t string entries.
  
  (** Control declarations and closures. *)
  Inductive cdecl : Type :=
  | CDecl (cs : cenv) (closure : eenv) (fs : fenv) (ins : ienv)
          (body : CD.d tags_t) (apply_block : ST.s tags_t)
  with cenv : Type :=
  | CEnv (cs : Env.t string cdecl).
  (**[]*)
  
  (** Control lookup. *)
  Definition clookup '(CEnv cs : cenv) : string -> option cdecl := (fun x => Env.find x cs).
  
  (** Bind an instance to an environment. *)
  Definition cupdate '(CEnv cs : cenv) (x : string) (d : cdecl) : cenv :=
    CEnv !{ x ↦ d ;; cs }!.
  (**[]*)
End StepDefs.
