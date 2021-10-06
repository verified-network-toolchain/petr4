Require Import Poulet4.Semantics Poulet4.Typed
        Poulet4.Syntax Coq.NArith.BinNat Coq.Lists.List.
Import ListNotations.
Require Poulet4.P4String.

Section TypingDefs.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  (** Typing context. *)
  Definition gamma : Type := @PathMap.t tags_t typ.

  (** TODO: is this correct? *)
  Definition typ_of_loc (l : Locator) (g : gamma) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   p => PathMap.get p g
    end.

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  (* TODO:
     What constraints do we need on:
     - fixed-width numeric types?
     - headers (unions & stacks)?
     - senum values: see comments below.
   *)
  Inductive val_typ (gsenum : genv_senum) : Sval -> typ -> Prop :=
  | typ_null : forall t, val_typ gsenum ValBaseNull t
  | typ_bool : forall b, val_typ gsenum (ValBaseBool b) TypBool
  | typ_integer : forall v, val_typ gsenum (ValBaseInteger v) TypInteger
  | typ_bit : forall v,
      val_typ gsenum (ValBaseBit v) (TypBit (N.of_nat (length v)))
  | typ_int : forall v,
      val_typ gsenum (ValBaseInt v) (TypInt (N.of_nat (length v)))
  | typ_varbit : forall n v,
      N.to_nat n < length v ->
      val_typ gsenum (ValBaseVarbit n v) (TypVarBit n)
  | typ_string : forall s,
      val_typ gsenum (ValBaseString s) TypString
  | typ_tuple : forall vs ts,
      Forall2 (val_typ gsenum) vs ts ->
      val_typ gsenum (ValBaseTuple vs) (TypTuple ts)
  | typ_record : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseRecord vs) (TypRecord ts)
  | typ_error : forall err,
      val_typ gsenum (ValBaseError err) TypError
  | typ_matchkind : forall mk,
      val_typ gsenum (ValBaseMatchKind mk) TypMatchKind
  | typ_struct : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseStruct vs) (TypStruct ts)
  | typ_header : forall b vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseHeader vs b) (TypHeader ts)
  | typ_union : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseUnion vs) (TypHeaderUnion ts)
  | typ_stack : forall s n vs ts,
      length vs = N.to_nat s ->
      Forall (fun v => val_typ gsenum v (TypHeader ts)) vs ->
      val_typ gsenum (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
  | typ_enumfield : forall ename member members,
      In member members ->
      val_typ gsenum
              (ValBaseEnumField ename member)
              (TypEnum ename None members)
  | typ_senumfield : forall ename member v t fields,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      AList.get fields member = Some v ->
      val_typ gsenum v t ->
      val_typ gsenum
              (ValBaseSenumField ename member v)
              (TypEnum ename (Some t) (List.map fst fields))
  (* TODO: what is a [ValBaseSenum _], and what is its type?
     It seems to be something in [gsenum],
     but should it be a value? *)
  | typ_senum : forall fields ename t,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      Forall (fun xv => val_typ gsenum (snd xv) t) fields ->
      val_typ
        gsenum (ValBaseSenum fields)
        (TypEnum ename (Some t) (List.map fst fields)).

  Definition envs_same (g : gamma) (st : state) : Prop :=
    forall p : path, PathMap.get p g = None <-> PathMap.get p (fst st) = None.

  Lemma envs_same_some_l : forall g st p t,
      envs_same g st -> PathMap.get p g = Some t ->
      exists v, PathMap.get p (fst st) = Some v.
  Proof.
    intros g st p t H Hgt; unfold envs_same in H.
    destruct (PathMap.get p (fst st)) as [v |] eqn:Heq; eauto.
    rewrite <- H, Hgt in Heq; discriminate.
  Qed.

  Lemma envs_same_some_r : forall g st p v,
      envs_same g st -> PathMap.get p (fst st) = Some v ->
      exists t, PathMap.get p g = Some t.
  Proof.
    intros g st p v H Hgt; unfold envs_same in H.
    destruct (PathMap.get p g) as [? |] eqn:Heq; eauto.
    rewrite H,Hgt in Heq; discriminate.
  Qed.
  
  Definition envs_type (gsenum : genv_senum) (g : gamma) (st : state) : Prop :=
    forall (p : path) (t : typ) (v : Sval),
      PathMap.get p g = Some t ->
      PathMap.get p (fst st) = Some v -> val_typ gsenum v t.

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)
  
  (** Expression typing. *)
  Definition expr_types (g : gamma) (e : expr) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      envs_same g st -> envs_type ge g st ->
      (exists v, run_expr ge read_one_bit p st e v) /\
      forall v, run_expr ge read_one_bit p st e v ->
           val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)

  (** Statement typing. *)
  Definition stmt_types (g g' : gamma) (s : stmt) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      envs_same g st -> envs_type ge g st ->
      (exists st' sig, run_stmt ge read_one_bit p st s st' sig) /\
      forall st' sig, run_stmt ge read_one_bit p st s st' sig ->
                 envs_same g' st' /\ envs_type ge g' st'.
End TypingDefs.

Notation "Γ '⊢e' e"
  := (expr_types Γ e) (at level 80, no associativity) : type_scope.
Notation "Γ1 '⊢s' s ⊣ Γ2"
  := (stmt_types Γ1 Γ2 s) (at level 80, no associativity) : type_scope.

(* TODO. *)
Section Soundness.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Variable (Γ : @gamma tags_t).

  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.

  Ltac soundtac :=
    autounfold with *;
    intros rob ge p st Henvs Henvt;
    split; eauto;
    try (intros v Hrn; inversion Hrn; subst; cbn; eauto).
  
  Lemma bool_sound : forall tag b dir,
      Γ ⊢e (MkExpression tag (ExpBool b) TypBool dir).
  Proof.
    intros; soundtac.
  Qed.
  
  Lemma arbitrary_int_sound : forall tag i z dir,
      Γ ⊢e
        (MkExpression
           tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir).
  Proof.
    intros; soundtac.
  Qed.

  Lemma unsigned_int_sound : forall tag i z w dir,
      Γ ⊢e
        (MkExpression
           tag (ExpInt (P4Int.Build_t _ i z (Some (w,false)))) (TypBit w) dir).
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma signed_int_sound : forall tag i z w dir,
      Γ ⊢e
        (MkExpression
           tag (ExpInt (P4Int.Build_t _ i z (Some (w,true)))) (TypInt w) dir).
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma string_sound : forall tag s dir,
      Γ ⊢e (MkExpression tag (ExpString s) TypString dir).
  Proof.
    intros; soundtac.
  Qed.

  Lemma name_sound : forall tag x loc t dir,
      typ_of_loc loc Γ = Some t ->
      Γ ⊢e (MkExpression tag (ExpName x loc) t dir).
  Proof.
    intros i x l t d Hgt; soundtac.
    - destruct l as [lp | lp]; simpl in Hgt;
        eapply envs_same_some_l in Hgt as [v Hv]; eauto.
      exists v. constructor; simpl.
      (** TODO:
          1. Need type preservation to [eval_val_to_sval].
          2. Perhaps [envs_same] needs to include [genv]. *)
      admit.
    - destruct l as [lp | lp]; simpl in Hgt;
        simpl in *; eauto.
  Admitted.

  (*Lemma array_access_sound : forall*)
End Soundness.
