Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.SmallStep.Value
        Poulet4.P4cub.Envn Poulet4.P4Arith
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Static.Static.
Import String.

Section StepDefs.
  Import TypeEquivalence ProperType
         F.FieldTactics P4ArithTactics
         AllCubNotations Env.EnvNotations.
  
  Context {tags_t : Type}.
  
  (** Expression environment. *)
  Definition eenv : Type := Env.t (string) (Expr.e tags_t).
  
  (** Bit-slicing. *)
  Definition eval_slice (hi lo : positive) (v : Expr.e tags_t) : option (Expr.e tags_t) :=
    match v with
    | <{ _ W z @ i }>
    | <{ _ S z @ i }>
      => let w' := (hi - lo + 1)%positive in
        Some $ Expr.EBit (Npos w')
             (BitArith.mod_bound (Npos w') $
              BitArith.bitstring_slice z hi lo) i
    | _ => None
    end.
  (**[]*)
  
  Definition eval_cast
             (target : Expr.t) (v : Expr.e tags_t) : option (Expr.e tags_t) :=
    match target, v with
    | (Expr.TBit (Npos 1)), <{ TRUE @ i }>         => Some (Expr.EBit 1%N 1%Z i)
    | (Expr.TBit (Npos 1)), <{ FALSE @ i }>        => Some (Expr.EBit 1%N 0%Z i)
    | {{ Bool }}, Expr.EBit 1%N 1%Z i => Some <{ TRUE @ i }>
    | {{ Bool }}, Expr.EBit 1%N 0%Z i => Some <{ FALSE @ i }>
    | {{ bit<w> }}, Expr.EInt _ z i
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
      => Some $ Expr.EStruct (combine (F.keys fs) vs) i
    | {{ hdr { fs } }}, <{ tup vs @ i }>
      => Some
          $ Expr.EHeader
          (combine (F.keys fs) vs) <{ TRUE @ i }> i
    | _, _ => None
    end.
  (**[]*)
  
  (** Default (value) Expression. *)
  Fail Fixpoint edefault (i : tags_t) (τ : Expr.t) : Expr.e tags_t :=
    let fix lstruct (ts : list (Expr.t)) : list (Expr.e tags_t) :=
        match ts with
        | []     => []
        | τ :: ts => edefault i τ :: lstruct ts
        end in
    let fix fstruct (fs : F.fs string (Expr.t))
        : F.fs string (Expr.t * Expr.e tags_t) :=
        match fs with
        | [] => []
        | (x, τ) :: fs => (x, edefault i τ) :: fstruct fs
        end in
    match τ with
    | {{ Bool }} => <{ BOOL false @ i }>
    | {{ bit<w> }} => Expr.EBit w 0%Z i
    | {{ int<w> }} => Expr.EInt w 0%Z i
    | {{ error }} => <{ Error None @ i }>
    | {{ matchkind }} => <{ Matchkind exact @ i }>
    | {{ tuple ts }} => Expr.ETuple (lstruct ts) i
    | {{ struct { fs } }} => Expr.EStruct (fstruct fs) i
    | {{ hdr { fs } }} => Expr.EHeader (fstruct fs) <{ BOOL false @ i }> i
    | {{ stack tfs[n] }}
      => let tefs := fstruct tfs in
        let hs :=
            repeat
            <{ hdr { tefs } valid:= BOOL false @ i @ i }>
            (Pos.to_nat n) in
        Expr.EHeaderStack tfs hs n 0%Z i
    end.
  (**[]*)
  
  (** Unary Operations. *)
  Definition eval_uop (op : Expr.uop) (e : Expr.e tags_t) : option (Expr.e tags_t) :=
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
    | _{ Size }_, <{ Stack _:_ nextIndex:=_ @ i }>
      => let w := 32%N in
        (* XXX need actual size instead of 0 here *)
        let s := Zpos xH in Some <{ w W s @ i }>
    | _{ Next }_, <{ Stack hs:_ nextIndex:=ni @ _ }>
      => nth_error hs $ Z.to_nat ni
    | _, _ => None
    end.
  (**[]*)
  
  (** Binary operations. *)
  Definition eval_bop
             (op : Expr.bop) (v1 v2 : Expr.e tags_t) (i : tags_t) : option (Expr.e tags_t) :=
    match op, v1, v2 with
    | +{ + }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.plus_mod w n1 n2) i
    | +{ + }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.plus_mod w z1 z2) i
    | +{ |+| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.plus_sat w n1 n2) i
    | +{ |+| }+,  <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.plus_sat w z1 z2) i
    | +{ - }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.minus_mod w n1 n2) i
    | +{ - }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.minus_mod w z1 z2) i
    | +{ |-| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.minus_sat w n1 n2) i
    | +{ |-| }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.minus_sat w z1 z2) i
    | +{ × }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.mult_mod w n1 n2) i
    | +{ × }+, <{ w S n1 @ _ }>, <{ _ S n2 @ _ }>
      => Some $ Expr.EInt w (IntArith.mult_mod w n1 n2) i
    | +{ << }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.shift_left w n1 n2) i
    | +{ << }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.shift_left w z1 z2) i
    | +{ >> }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.shift_right w n1 n2) i
    | +{ >> }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.shift_right w z1 z2) i
    | +{ & }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.bit_and w n1 n2) i
    | +{ & }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.bit_and w z1 z2) i
    | +{ ^ }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.bit_xor w n1 n2) i
    | +{ ^ }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.bit_xor w z1 z2) i
    | +{ | }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
      => Some $ Expr.EBit w (BitArith.bit_or w n1 n2) i
    | +{ | }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
      => Some $ Expr.EInt w (IntArith.bit_or w z1 z2) i
    | +{ <= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ Expr.EBool (n1 <=? n2)%Z i
    | +{ <= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ Expr.EBool (z1 <=? z2)%Z i
    | +{ < }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ Expr.EBool (n1 <? n2)%Z i
    | +{ < }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ Expr.EBool (z1 <? z2)%Z i
    | +{ >= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ Expr.EBool (n2 <=? n1)%Z i
    | +{ >= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ Expr.EBool (z2 <=? z1)%Z i
    | +{ > }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ Expr.EBool (n2 <? n1)%Z i
    | +{ > }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ Expr.EBool (z2 <? z1)%Z i
    | +{ && }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ Expr.EBool (b1 && b2) i
    | +{ || }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ Expr.EBool (b1 || b2) i
    | +{ == }+, _, _ => Some $ Expr.EBool (ExprEquivalence.eqbe v1 v2) i
    | +{ != }+, _, _ => Some $ Expr.EBool (negb $ ExprEquivalence.eqbe v1 v2) i
    | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
      => Some $ Expr.EBit (w1 + w2)%N (BitArith.concat w1 w2 n1 n2) i
    | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 S n2 @ _ }>
      => Some $ Expr.EBit (w1 + Npos w2)%N (BitArith.concat w1 (Npos w2) n1 n2) i
    | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 S n2 @ _ }>
      => Some $ Expr.EInt (w1 + w2)%positive (IntArith.concat (Npos w1) (Npos w2) n1 n2) i
    | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 W n2 @ _ }>
      =>
      match w2 with
      | 0%N => 
        Some (Expr.EInt w1 n1 i)
      | Npos w2 =>
        Some $ Expr.EInt (w1 + w2)%positive (IntArith.concat (Npos w1) (Npos w2) n1 n2) i
      end
    | _, _, _ => None
    end.
  (**[]*)
  
  (** Get header stack data from value. *)
  Definition header_stack_data (v : Expr.e tags_t)
    : option (Z * F.fs string (Expr.t) * (list (Expr.e tags_t))) :=
    match v with
    | <{ Stack hs:ts nextIndex:=ni @ _}> => Some (ni,ts,hs)
    | _ => None
    end.
  (**[]*)
  
  Definition eval_member (x : string) (v : Expr.e tags_t) : option (Expr.e tags_t) :=
    match v with
    | <{ struct { vs } @ _ }>
    | <{ hdr { vs } valid:=_ @ _ }> => vs ▷ F.get x
    | _                             => None
    end.
  (**[]*)

  (** Header stack access. *)
  Definition eval_access (v : Expr.e tags_t) (n : Z) : option (Expr.e tags_t) :=
    v
      ▷ header_stack_data
      >>| triple_3
      >>= (fun hs => nth_error hs (Z.to_nat n)).
  
  Section Edefault.
    Local Hint Constructors value : core.
    
    Fail Lemma value_edefault : forall i τ, value (edefault i τ).
    (*Proof.
      induction τ using custom_t_ind; unravel; auto 1;
        try (constructor; apply repeat_Forall); constructor; auto 1;
          try (ind_list_predfs; unfold F.predfs_data in * );
          try ind_list_Forall; unravel in *; auto 4.
    Qed. *)   
  End Edefault.
  
  Section HelpersType.
    Local Hint Constructors check_expr : core.
    Local Hint Extern 0 => bit_bounded : core.
    Local Hint Extern 0 => int_bounded : core.
    
    Import CanonicalForms.
    
    Lemma eval_slice_types : forall D Γ v v' τ hi lo w,
        eval_slice hi lo v = Some v' ->
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⟦ D, Γ ⟧ ⊢ v ∈ τ ->
        let w' := (Npos hi - Npos lo + 1)%N in
        ⟦ D, Γ ⟧ ⊢ v' ∈ bit<w'>.
    Proof.
      intros D Γ v v' τ hi lo w Heval Hv Hw Hnum Ht w'; subst w';
        inv Hnum; assert_canonical_forms; unravel in *; inv Heval; auto 2.
    Admitted.
    
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    
    Lemma eval_cast_types : forall D Γ τ τ' v v',
        eval_cast τ' v = Some v' ->
        value v ->
        proper_cast τ τ' ->
        ⟦ D, Γ ⟧ ⊢ v ∈ τ ->
        ⟦ D, Γ ⟧ ⊢ v' ∈ τ'.
    Proof.
      intros D Γ τ τ' v v' Heval Hv Hpc Ht;
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
            unravel; try apply IHx; auto 2. (*
      - inv Heval; constructor; auto 1.
        + apply pn_header. rewrite F.predfs_data_map. assumption.
        + clear x0 H0. generalize dependent fs.
          ind_list_Forall; intros [| [? ?] ?] ? ;
            unravel in *; try inv_Forall2_cons;
              constructor; try split;
                unravel; try apply IHx; auto 2.
         *) *)
    
    Lemma eval_bop_types : forall Γ D op τ1 τ2 τ (i : tags_t) v1 v2 v,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        eval_bop op v1 v2 i = Some v ->
        ⟦ D, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ D, Γ ⟧ ⊢ v2 ∈ τ2 -> ⟦ D, Γ ⟧ ⊢ v ∈ τ.
    Proof.
      intros Γ D op τ1 τ2 τ v1 v2 v i Hbop Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbop; unravel in *; try inv_numeric;
          repeat assert_canonical_forms;
          try (inv_numeric_width; assert_canonical_forms);
          try (inv Heval; auto 2; assumption).
    Qed.
    
    Lemma eval_member_types : forall D Γ x v v' ts τ τ',
        eval_member x v = Some v' ->
        value v ->
        member_type ts τ ->
        F.get x ts = Some τ' ->
        ⟦ D, Γ ⟧ ⊢ v ∈ τ ->
        ⟦ D, Γ ⟧ ⊢ v' ∈ τ'.
    Proof.
      intros D Γ x v v' ts τ τ' Heval Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms.
      - eapply F.relfs_get_r in H1 as [? [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
            unravel in *; inv Heval; intuition.
      - eapply F.relfs_get_r in H6 as [? [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
            unravel in *; inv Heval; intuition.
    Qed.
    
    Local Hint Constructors proper_nesting : core.
    Hint Rewrite repeat_length.
    Local Hint Resolve proper_inside_header_nesting : core.
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    
    Fail Lemma edefault_types : forall D Γ i τ,
        PT.proper_nesting τ ->
        let e := edefault i τ in
        ⟦ D, Γ ⟧ ⊢ e ∈ τ.
    (*Proof.
      intros; subst e; induction τ using custom_t_ind; unravel;
        invert_proper_nesting; auto 2;
          constructor; autorewrite with core; auto 2;
            try (apply repeat_Forall; constructor; auto 2);
            try (ind_list_Forall; repeat inv_Forall_cons; constructor; intuition);
            try (ind_list_predfs; repeat invert_cons_predfs; constructor;
                 try split; unravel; intuition).
                 Qed.*)
    
    Local Hint Resolve Forall_impl : core.
    Local Hint Resolve Forall_firstn : core.
    Local Hint Resolve Forall_skipn : core.
    Local Hint Resolve proper_inside_header_nesting : core.
    Fail Local Hint Resolve edefault_types : core.
    Hint Rewrite app_length.
    Hint Rewrite Forall_app.
    Hint Rewrite firstn_length_le.
    Hint Rewrite skipn_length.
    Hint Rewrite map_length.
    Hint Rewrite (@F.predfs_data_map string).
    Hint Rewrite @F.map_fst.
    Hint Rewrite @map_compose.
    Hint Rewrite (@Forall2_map_l Expr.t).
    Hint Rewrite (@Forall2_Forall Expr.t).
    Hint Rewrite (@F.predfs_data_map).
    Hint Rewrite @F.relfs_split_map_iff.
    Hint Rewrite @F.map_snd.
    
    Lemma eval_uop_types : forall D Γ op e v τ τ',
        uop_type op τ τ' -> value e -> eval_uop op e = Some v ->
        ⟦ D, Γ ⟧ ⊢ e ∈ τ -> ⟦ D, Γ ⟧ ⊢ v ∈ τ'.
    (*Proof.
      intros D Γ op e v τ τ' Huop Hev Heval Het;
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
    Qed.*)
    Admitted.
  End HelpersType.
  
  Section HelpersExist.
    Import CanonicalForms.
    
    Lemma eval_slice_exists : forall D Γ v τ hi lo w,
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⟦ D, Γ ⟧ ⊢ v ∈ τ ->
        exists v', eval_slice hi lo v = Some v'.
    Proof.
      intros D Γ v τ hi lo w Hv Hw Hnum Ht;
        inv Hnum; assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_cast_exists : forall D Γ e τ τ',
        value e ->
        proper_cast τ τ' ->
        ⟦ D, Γ ⟧ ⊢ e ∈ τ ->
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
    
    Lemma eval_bop_exists : forall D Γ op τ1 τ2 τ (i : tags_t) v1 v2,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        ⟦ D, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ D, Γ ⟧ ⊢ v2 ∈ τ2 ->
        exists v, eval_bop op v1 v2 i = Some v.
    Proof.
      intros D Γ op τ1 τ2 τ i v1 v2 Hbop Hv1 Hv2 Ht1 Ht2;
        inv Hbop; try inv_numeric; try inv_numeric_width;
          repeat assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_uop_exists : forall op D Γ e τ τ',
        uop_type op τ τ' -> value e -> ⟦ D, Γ ⟧ ⊢ e ∈ τ ->
        exists v, eval_uop op e = Some v.
    (* Proof.
      intros op D Γ e τ τ' Hu Hv Het; inv Hu;
        try inv_numeric; assert_canonical_forms;
          unravel; eauto 2.
      - assert (Hnihs : (Z.to_nat x0 < length x)%nat) by lia.
        pose proof nth_error_exists _ _ Hnihs as [? Hnth].
        rewrite Hnth; eauto 2.
      - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
      - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
    Qed. *)
    Admitted.
      
    Lemma eval_member_exists : forall D Γ x v ts τ τ',
        value v ->
        member_type ts τ ->
        F.get x ts = Some τ' ->
        ⟦ D, Γ ⟧ ⊢ v ∈ τ ->
        exists v', eval_member x v = Some v'.
    Proof.
      intros D Γ x v ts τ τ' Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms; unravel.
      - eapply F.relfs_get_r in H1 as [? [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
      - eapply F.relfs_get_r in H6 as [? [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
    Qed.
  End HelpersExist.
  
  (** Lookup an lvalue. *)
  Fixpoint lv_lookup (ϵ : eenv) (lv : Expr.e tags_t) : option (Expr.e tags_t) :=
    match lv with
    | <{ Var x:_ @ _ }> => Env.find x ϵ
    | <{ Mem lv dot x : _ @ _ }> =>
      (* TODO: use monadic bind. *)
      match lv_lookup ϵ lv with
      | Some <{ struct { fs } @ _ }>
      | Some <{ hdr { fs } valid:=_  @ _ }> => fs ▷ F.get x
      | _ => None
      end
    | <{ Access lv[n] : _ @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ Stack vss:_ nextIndex:=_ @ _ }> => nth_error vss (Z.to_nat n)
      | _ => None
      end
    | _ => None
    end.
  (**[]*)
  
  (** Updating an lvalue in an environment. *)
  Fixpoint lv_update (lv v : Expr.e tags_t) (ϵ : eenv) : eenv :=
    match lv with
    | <{ Var x:_ @ _ }> => !{ x ↦ v ;; ϵ }!
    | <{ Mem lv dot x : _ @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ struct { vs } @ i }>
        => lv_update lv (Expr.EStruct (F.update x v vs) i) ϵ
      | Some <{ hdr { vs } valid:=b @ i }>
        => lv_update lv (Expr.EHeader (F.update x v vs) b i) ϵ
      | _ => ϵ
      end
    | <{ Access lv[n] : _ @ _ }> =>
      match lv_lookup ϵ lv with
      | Some <{ Stack vss:ts nextIndex:=ni @ i }> =>
        let vss := nth_update (Z.to_nat n) v vss in
        lv_update lv <{ Stack vss:ts nextIndex:=ni @ i }> ϵ
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
             (argsv : Expr.args tags_t)
             (ϵcall : eenv) : eenv -> eenv :=
    F.fold (fun x arg ϵ =>
              match arg with
              | PAIn v     => !{ x ↦ v ;; ϵ }!
              | PAInOut lv => match lv_lookup ϵcall lv with
                                   | None   => ϵ
                                   | Some v => !{ x ↦ v ;; ϵ }!
                                   end
              | PAOut _    => ϵ
              | PADirLess _ => ϵ (*what to do with directionless param*)
              end) argsv.
  (**[]*)
  
  (** Update call-site environment with
      out variables from function call evaluation. *)
  Definition copy_out
             (argsv : Expr.args tags_t)
             (ϵf : eenv) : eenv -> eenv :=
    F.fold (fun x arg ϵ =>
              match arg with
              | PADirLess _ => ϵ (*what to do with directionless param*)
              | PAIn _ => ϵ
              | PAOut lv
              | PAInOut lv =>
                match Env.find x ϵf with
                | None   => ϵ
                | Some v => lv_update lv v ϵ
                end
              end) argsv.
  (**[]*)
  
  (** Table environment. *)
  Definition tenv : Type := Env.t string (Control.table tags_t).
  
  (** Function declarations and closures. *)
  Inductive fdecl : Type :=
  | FDecl (closure : eenv) (fs : fenv) (ins : ienv) (body : Stmt.s tags_t)
  with fenv : Type :=
  | FEnv (fs : Env.t string fdecl)
  (** Action declarations and closures *)
  with adecl : Type :=
  | ADecl (closure : eenv) (fs : fenv) (ins : ienv) (aa : aenv) (body : Stmt.s tags_t)
  with aenv : Type :=
  | AEnv (aa : Env.t string adecl)
  (** Instances and Environment. *)
  with inst : Type :=
  | CInst (closure : eenv) (fs : fenv) (ins : ienv)
          (tbls : tenv) (aa : aenv)
          (apply_blk : Stmt.s tags_t)  (* control instance *)
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
    list (Expr.e tags_t * Expr.matchkind) ->
    list string ->
    string * Expr.args tags_t.
  (**[]*)
  
  (** Control plane configuration. *)
  Definition ctrl : Type := Env.t string entries.
  
  (** Control declarations and closures. *)
  Inductive cdecl : Type :=
  | CDecl (cs : cenv) (closure : eenv) (fs : fenv) (ins : ienv)
          (body : Control.d tags_t) (apply_block : Stmt.s tags_t)
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
