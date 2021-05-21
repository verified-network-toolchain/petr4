Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Require Import Poulet4.P4Arith.
Require Export Poulet4.P4cub.Syntax.AST.
Module P := P4cub.
Import P.P4cubNotations.

Module E := P.Expr.
Module F := P.F.
Module PR := P.Parser.

Module TE := E.TypeEquivalence.

Require Poulet4.P4cub.Static.Check.

(** Notation entries. *)
Declare Custom Entry p4value.
Declare Custom Entry p4lvalue.

Module Val.
  (** Values from expression evaluation. *)
  Inductive v : Type :=
  | VBool (b : bool)
  | VInt (w : positive) (n : Z)
  | VBit (w : positive) (n : Z)
  | VTuple (vs : list v)
  | VRecord (fs : F.fs string v)
  | VHeader (fs : F.fs string v) (validity : bool)
  | VError (err : option string)
  | VMatchKind (mk : P4cub.Expr.matchkind)
  | VHeaderStack (ts : F.fs string E.t)
                 (headers : list (bool * F.fs string v))
                 (size : positive) (nextIndex : Z).
  (**[]*)

  (** Lvalues. *)
  Inductive lv : Type :=
  | LVVar (x : string)                 (* Local variables. *)
  | LVMember (arg : lv) (x : string) (* Member access. *)
  | LVAccess (stk : lv) (index : Z)       (* Header stack indexing. *).
  (**[]*)

  (** Evaluated arguments. *)
  Definition argsv : Type := F.fs string (P4cub.paramarg v lv).

  (** Intial/Default value from a type. *)
  Fixpoint vdefault (τ : E.t) : v :=
      let fix lrec (ts : list E.t) : list v :=
          match ts with
          | [] => []
          | τ :: ts => vdefault τ :: lrec ts
          end in
      let fix fields_rec
              (ts : F.fs string E.t) : F.fs string v :=
          match ts with
          | [] => []
          | (x, τ) :: ts => (x, vdefault τ) :: fields_rec ts
          end in
      match τ with
      | {{ error }}      => VError None
      | {{ matchkind }}  => VMatchKind E.MKExact
      | {{ Bool }}       => VBool false
      | {{ bit<w> }}     => VBit w 0%Z
      | {{ int<w> }}     => VInt w 0%Z
      | {{ tuple ts }}   => VTuple (lrec ts)
      | {{ rec { ts } }} => VRecord (fields_rec ts)
      | {{ hdr { ts } }} => VHeader (fields_rec ts) false
      | {{ stack fs[n] }} => VHeaderStack
                              fs (repeat (false, fields_rec fs)
                                         (Pos.to_nat n)) n 0
      end.
    (**[]*)

  (** A custom induction principle for value. *)
  Section ValueInduction.
    Variable P : v -> Prop.

    Hypothesis HVBool : forall b, P (VBool b).

    Hypothesis HVBit : forall w n, P (VBit w n).

    Hypothesis HVInt : forall w n, P (VInt w n).

    Hypothesis HVTuple : forall vs,
        Forall P vs -> P (VTuple vs).

    Hypothesis HVRecord : forall fs,
        Field.predfs_data P fs -> P (VRecord fs).

    Hypothesis HVHeader : forall fs b,
        Field.predfs_data P fs -> P (VHeader fs b).

    Hypothesis HVError : forall err, P (VError err).

    Hypothesis HVMatchKind : forall mk, P (VMatchKind mk).

    Hypothesis HVHeaderStack : forall ts hs size ni,
        Forall (Field.predfs_data P ∘ snd) hs -> P (VHeaderStack ts hs size ni).

    Definition custom_value_ind : forall v' : v, P v' :=
      fix custom_value_ind (val : v) : P val :=
        let fix lind (vs : list v) : Forall P vs :=
            match vs with
            | [] => Forall_nil _
            | hv :: vs => Forall_cons _ (custom_value_ind hv) (lind vs)
            end in
        let fix fields_ind
                (flds : F.fs string v) : Field.predfs_data P flds :=
            match flds as fs return Field.predfs_data P fs with
            | [] => Forall_nil (Field.predf_data P)
            | (_, hfv) as hf :: tf =>
              Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
            end in
        let fix ffind
                (fflds : list (bool * Field.fs string v))
            : Forall (Field.predfs_data P ∘ snd) fflds :=
            match fflds as ffs
                  return Forall (Field.predfs_data P ∘ snd) ffs with
            | [] => Forall_nil (Field.predfs_data P ∘ snd)
            | (_, vs) as bv :: ffs => Forall_cons bv (fields_ind vs) (ffind ffs)
            end in
        match val as v' return P v' with
        | VBool b  => HVBool b
        | VInt w n => HVInt w n
        | VBit w n => HVBit w n
        | VTuple vs      => HVTuple vs (lind vs)
        | VRecord vs     => HVRecord vs (fields_ind vs)
        | VHeader vs b   => HVHeader vs b (fields_ind vs)
        | VError err     => HVError err
        | VMatchKind mk  => HVMatchKind mk
        | VHeaderStack ts hs size ni => HVHeaderStack ts hs size ni (ffind hs)
        end.
  End ValueInduction.

  Module ValueEquality.
    Import Field.FieldTactics.

    Section VE.
    (** Computational Value equality *)
    Fixpoint eqbv (v1 v2 : v) : bool :=
      let fix lrec (vs1 vs2 : list v) : bool :=
          match vs1, vs2 with
          | [], [] => true
          | v1::vs1, v2::vs2 => eqbv v1 v2 && lrec vs1 vs2
          | [], _::_ | _::_, [] => false
          end in
      let fix fields_rec (vs1 vs2 : Field.fs string v) : bool :=
          match vs1, vs2 with
          | [],           []           => true
          | (x1, v1)::vs1, (x2, v2)::vs2
            => equiv_dec x1 x2 &&&& eqbv v1 v2 && fields_rec vs1 vs2
          | [],            _::_
          | _::_,           []          => false
          end in
      let fix ffrec (v1ss v2ss : list (bool * Field.fs string v)) : bool :=
          match v1ss, v2ss with
          | [], _::_ | _::_, [] => false
          | [], [] => true
          | (b1,vs1) :: v1ss, (b2, vs2) :: v2ss => (eqb b1 b2)%bool &&
                                                fields_rec vs1 vs2 &&
                                                ffrec v1ss v2ss
          end in
      match v1, v2 with
      | VBool b1,       VBool b2       => eqb b1 b2
      | VInt w1 z1,     VInt w2 z2     => (w1 =? w2)%positive &&
                                         (z1 =? z2)%Z
      | VBit w1 n1,     VBit w2 n2     => (w1 =? w2)%positive &&
                                         (n1 =? n2)%Z
      | VMatchKind mk1, VMatchKind mk2 => if equiv_dec mk1 mk2
                                         then true
                                         else false
      | VError err1,    VError err2    => if equiv_dec err1 err2
                                         then true
                                         else false
      | VTuple vs1, VTuple vs2         => lrec vs1 vs2
      | VHeader vs1 b1, VHeader vs2 b2 => (eqb b1 b2)%bool && fields_rec vs1 vs2
      | VRecord vs1,    VRecord vs2    => fields_rec vs1 vs2
      | VHeaderStack ts1 vss1 n1 ni1,
        VHeaderStack ts2 vss2 n2 ni2   => F.eqb_fs TE.eqbt ts1 ts2 &&
                                         (n1 =? n2)%positive && (ni1 =? ni2)%Z &&
                                         ffrec vss1 vss2
      | _,              _              => false
      end.
    (**[]*)

    Lemma eqbv_refl : forall vl : v, eqbv vl vl = true.
    Proof.
      Hint Rewrite eqb_reflx.
      Hint Rewrite Pos.eqb_refl.
      Hint Rewrite equiv_dec_refl.
      Hint Rewrite Z.eqb_refl.
      Hint Rewrite TE.eqbt_refl.
      Hint Rewrite (@F.eqb_fs_reflx string E.t).
      Hint Rewrite andb_true_r.
      Hint Extern 0 => equiv_dec_refl_tactic : core.
      induction vl using custom_value_ind; simpl in *;
      autorewrite with core; simpl; auto;
      try match goal with
        | hs: list (bool * F.fs string v),
          H: Forall _ ?hs
          |- _ => induction hs as [| [? ?] ? ?];
                try inv_Forall_cons;
                autorewrite with core;
                unfold "∘" in *; simpl in *; intuition;
                repeat (rewrite_true; simpl);
                autorewrite with core;
                match goal with
                | H: Forall _ ?hs |- _ => clear H hs
                end
        end;
      try ind_list_Forall; try ind_list_predfs;
      intuition; autorewrite with core; simpl;
      repeat (rewrite_true; simpl); auto.
    Qed.

    Import F.RelfEquiv.

    Ltac eq_true_terms :=
      match goal with
      | H: eqb _ _ = true |- _
        => apply eqb_prop in H; subst
      | H: (_ =? _)%positive = true |- _
        => apply Peqb_true_eq in H; subst
      | H: (_ =? _)%Z = true |- _
        => apply Z.eqb_eq in H; subst
      | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
        => destruct (equiv_dec x1 x2) as [? | ?];
          simpl in H; try discriminate
      | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
        => destruct (equiv_dec t1 t2) as [? | ?];
          simpl in H; try discriminate
      | H: relop _ _ _ |- _ => inv H
      | H: F.eqb_fs TE.eqbt _ _ = true
        |- _ => pose proof eqb_fs_equiv _ _ TE.eqbt_reflect _ _ H as ?; clear H
      | H: F.relfs eq _ _ |- _ => apply eq_relfs in H; subst
      end.
    (**[]*)

    Ltac eauto_too_dumb :=
      match goal with
      | H: ?f ?x ?y = ?z,
           IH: (forall y, ?f ?x y = ?z -> _)
        |- _ => apply IH in H; clear IH
      end.

    Lemma eqbv_eq : forall v1 v2 : v, eqbv v1 v2 = true -> v1 = v2.
    Proof.
      induction v1 using custom_value_ind; intros []; intros;
      simpl in *; try discriminate;
      repeat destruct_andb;
      repeat (eq_true_terms); unfold equiv in *; auto; f_equal;
      repeat (eq_true_terms); auto;
      try match goal with
          | hs1: list (bool * F.fs string v),
            IH: Forall _ ?hs1,
            H: _ ?hs1 ?hs2 = true
            |- ?hs1 = ?hs2 => generalize dependent hs2;
                            induction hs1 as [| [? ?] ? ?];
                            intros [| [? ?] ?]; intros; simpl in *;
                            try discriminate; auto;
                            repeat destruct_andb; inv_Forall_cons;
                            repeat eq_true_terms; unfold "∘" in *;
                            simpl in *; intuition;
                            eauto_too_dumb; subst; repeat f_equal;
                            match goal with
                            | H: Forall _ ?l |- _ => clear H l
                            end
          end;
      try match goal with
        | IH: Forall _ ?vs1,
          H: _ ?vs1 ?vs2 = true
          |- ?vs1 = ?vs2 => generalize dependent vs2;
                          induction vs1; intros []; intros;
                          try discriminate; try inv_Forall_cons;
                          repeat destruct_andb; intuition;
                          repeat eauto_too_dumb; subst; auto
        end;
      try match goal with
        | IH: F.predfs_data _ ?fs1,
          H: _ ?fs1 ?fs2 = true
          |- ?fs1 = ?fs2 => generalize dependent fs2;
                          induction fs1; intros [| [? ?] ?]; intros;
                          try discriminate; try invert_cons_predfs;
                          try destruct_lifted_andb;
                          repeat destruct_andb; intuition;
                          unfold equiv in *; subst;
                          repeat eauto_too_dumb; subst; auto
        end.
    Qed.

    Lemma eqbv_eq_iff : forall v1 v2 : v, eqbv v1 v2 = true <-> v1 = v2.
    Proof.
      Hint Resolve eqbv_refl : core.
      Hint Resolve eqbv_eq : core.
      intros; split; intros; subst; auto.
    Qed.

    Lemma eqbv_reflect : forall v1 v2, reflect (v1 = v2) (eqbv v1 v2).
    Proof.
      Hint Resolve eqbv_eq_iff : core.
      intros; reflect_split; auto; subst.
      rewrite eqbv_refl in Heqb; discriminate.
    Qed.
    End VE.

    Instance ValueEqDec : EqDec v eq :=
      { equiv_dec := fun v1 v2 => reflect_dec _ _ (eqbv_reflect v1 v2) }.
    (**[]*)
  End ValueEquality.

Module ValueNotations.
  Notation "'~{' val '}~'" := val (val custom p4value at level 99).
  Notation "( x )" := x (in custom p4value, x at level 99).
  Notation "x" := x (in custom p4value at level 0, x constr at level 0).
  Notation "'TRUE'" := (VBool true) (in custom p4value at level 0).
  Notation "'FALSE'" := (VBool false) (in custom p4value at level 0).
  Notation "'VBOOL' b" := (VBool b) (in custom p4value at level 0).
  Notation "w 'VW' n" := (VBit w n) (in custom p4value at level 0).
  Notation "w 'VS' n" := (VInt w n) (in custom p4value at level 0).
  Notation "'TUPLE' vs" := (VTuple vs) (in custom p4value at level 0).
  Notation "'REC' { fs }" := (VRecord fs)
                               (in custom p4value at level 6,
                                   no associativity).
  Notation "'HDR' { fs } 'VALID' ':=' b" := (VHeader fs b)
                               (in custom p4value at level 6,
                                   no associativity).
  Notation "'ERROR' x" := (VError x) (in custom p4value at level 0).
  Notation "'MATCHKIND' mk"
    := (VMatchKind mk)
         (in custom p4value at level 0, mk custom p4matchkind).
  Notation "'STACK' vs : ts [ n ] 'NEXT' ':=' ni"
           := (VHeaderStack ts vs n ni)
                (in custom p4value at level 0, no associativity).
End ValueNotations.

Module LValueNotations.
  Notation "'l{' lval '}l'" := lval (lval custom p4lvalue at level 99).
  Notation "( x )" := x (in custom p4lvalue, x at level 99).
  Notation "x" := x (in custom p4lvalue at level 0, x constr at level 0).
  Notation "'VAR' x" := (LVVar x) (in custom p4lvalue at level 0).
  Notation "lval 'DOT' x"
    := (LVMember lval x) (in custom p4lvalue at level 1,
                             lval custom p4lvalue).
  Notation "lval [ n ]"
           := (LVAccess lval n) (in custom p4lvalue at level 1,
                                   lval custom p4lvalue).
End LValueNotations.

Module ValueUtil.
  Import ValueNotations.

  Fixpoint match_pattern (p : PR.pat) (V : v) : bool :=
    match p, V with
    | [{ ?? }], _ => true
    | [{ (w PW a) &&& (_ PW b) }], ~{ _ VW c }~
      => Z.land a b =? Z.land c b
    | [{ (w PW a) .. (_ PW b) }], ~{ _ VW c }~
      => (a <=? c)%Z && (c <=? b)%Z
    | [{ w1 PW n1 }], ~{ w2 VW n2 }~ =>
      (w1 =? w2)%positive && (n1 =? n2)%Z
    | [{ w1 PS n1 }], ~{ w2 VS n2 }~ =>
      (w1 =? w2)%positive && (n1 =? n2)%Z
    | [{ PTUP ps }], ~{ TUPLE vs }~ =>
      (fix F ps vs :=
         match ps, vs with
         | [], [] => true
         | p::ps, v::vs => match_pattern p v && F ps vs
         | _, _ => false
         end) ps vs
    | _,_ => false
    end.
  (**[]*)
  
  Section Util.
    Context {tags_t : Type}.

    (* TODO: uhhh... *)
    Fail Fixpoint expr_of_value (i : tags_t) (V : v) : E.e tags_t :=
      let fix lrec (vs : list v) : list (E.e tags_t) :=
          match vs with
          | []      => []
          | hv :: tv => expr_of_value i hv :: lrec tv
          end in
      let fix frec (vs : F.fs string v)
          : F.fs string (E.t * E.e tags_t) :=
          match vs with
          | [] => []
          | (x, hv) :: vs => (x, (_, expr_of_value i hv)) :: frec vs (* TODO *)
          end in
      let fix stkrec (hs : list (bool * F.fs string v))
          : list (E.e tags_t) :=
          match hs with
          | [] => []
          | (b, vs) :: hs
            => E.EHeader (frec vs) <{ BOOL b @ i }> i :: stkrec hs
          end in
      match V with
      | ~{ VBOOL b }~ => <{ BOOL b @ i }>
      | ~{ w VW n }~ => <{ w W n @ i }>
      | ~{ w VS z }~ => <{ w S z @ i }>
      | ~{ ERROR err }~ => <{ Error err @ i }>
      | ~{ MATCHKIND mk }~ => <{ Matchkind mk @ i }>
      | ~{ TUPLE vs }~ => E.ETuple (lrec vs) i
      | ~{ REC { vs } }~ => E.ERecord (frec vs) i
      | ~{ HDR { vs } VALID:=b }~
        => E.EHeader (frec vs) <{ BOOL b @ i }> i
      | ~{ STACK vs:ts[n] NEXT:=ni }~
        => E.EHeaderStack ts (stkrec vs) n ni
      end.
  End Util.
End ValueUtil.

Module ValueTyping.
  Import E.ProperType.
  Import ValueNotations.
  Import LValueNotations.
  Import Check.Typecheck.TypeCheckDefs.

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
  | typ_rec (vs : Field.fs string v)
            (ts : Field.fs string E.t) :
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      ∇ errs ⊢ REC { vs } ∈ rec { ts }
  | typ_hdr (vs : Field.fs string v) (b : bool)
            (ts : Field.fs string E.t) :
      proper_nesting {{ hdr { ts } }} ->
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }
  | typ_error (err : option string) :
      match err with
      | None => True
      | Some err => errs err = Some tt
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
        | Some err => errs err = Some tt
        end ->
        P errs ~{ ERROR err }~ {{ error }}.

    Hypothesis HTuple : forall errs vs ts,
        Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts ->
        Forall2 (P errs) vs ts ->
        P errs ~{ TUPLE vs }~ {{ tuple ts }}.

    Hypothesis HRecord : forall errs vs ts,
        Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
        Field.relfs (fun vl τ => P errs vl τ) vs ts ->
        P errs ~{ REC { vs } }~ {{ rec { ts } }}.

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
            | typ_rec _ _ _ Hfs => HRecord _ _ _ Hfs (fsind Hfs)
            | typ_hdr _ _ b _ HP Hfs => HHeader _ _ b _ HP Hfs (fsind Hfs)
            | typ_headerstack _ _ _ _ _ Hn Hni Hlen HP
                              Hhs => HStack _ _ _ _ _ Hn Hni
                                           Hlen HP
                                           Hhs (hsind Hhs)
            end.
  End ValueTypingInduction.

  Inductive type_lvalue (Γ : gamma) : lv -> E.t -> Prop :=
  | typ_var (x : string) (τ : E.t) :
      Γ x = Some τ ->
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
    induction τ using E.custom_t_ind; simpl; constructor;
    try invert_proper_nesting;
    autorewrite with core; auto; try lia;
    try (ind_list_Forall; repeat inv_Forall_cons;
         constructor; intuition; assumption);
    try (apply repeat_Forall; unravel; constructor);
    try (ind_list_predfs; repeat invert_cons_predfs;
         constructor; try split; unravel;
         intuition; assumption); auto.
  Qed.
End ValueTyping.
End Val.
