(* TODO: UNDER MAINTENANCE
Require Export P4cub.Check.
Require Export P4cub.P4Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.

Reserved Notation "'ℵ' env '**' e1 '-->' e2"
         (at level 40, e1 custom p4expr, e2 custom p4expr).

(** * Small-Step Values *)
Module IsValue.
  Module P := P4cub.
  Module E := P.Expr.
  Module F := P.F.

  Import P.P4cubNotations.

  Inductive value {tags_t : Type} : E.e tags_t -> Prop :=
  | value_bool (b : bool) (i : tags_t) :
      value <{ BOOL b @ i }>
  | value_bit (w : positive) (n : N) (i : tags_t) :
      value <{ w W n @ i }>
  | value_int (w : positive) (z : Z) (i : tags_t) :
      value <{ w S z @ i }>
  | value_tuple (es : list (E.e tags_t)) (i : tags_t) :
      Forall value es ->
      value <{ tup es @ i }>
  | value_record (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
                 (i : tags_t) :
      F.predfs_data (value ∘ snd) fs ->
      value <{ rec { fs } @ i }>
  | value_header (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
                 (b : E.e tags_t) (i : tags_t) :
      value b ->
      F.predfs_data (value ∘ snd) fs ->
      value <{ hdr { fs } valid:=b @ i }>
  | value_error (err : option (string tags_t)) (i : tags_t) :
      value <{ Error err @ i }>
  | value_matchkind (mk : E.matchkind) (i : tags_t) :
      value <{ Matchkind mk @ i }>
  | value_headerstack (fs : F.fs tags_t (E.t tags_t))
                      (hs : list (E.e tags_t)) (n : positive)
                      (ni : N) :
      Forall value hs ->
      value <{ Stack hs:fs[n] nextIndex:=ni }>.

  Section IsValueInduction.
    Variable tags_t : Type.

    Variable P : E.e tags_t -> Prop.

    Hypothesis HBool : forall b i, P <{ BOOL b @ i }>.

    Hypothesis HBit : forall w n i, P <{ w W n @ i }>.

    Hypothesis HInt : forall w z i, P <{ w S z @ i }>.

    Hypothesis HTuple : forall es i,
      Forall value es ->
      Forall P es ->
      P <{ tup es @ i }>.

    Hypothesis HRecord : forall fs i,
        F.predfs_data (value ∘ snd) fs ->
        F.predfs_data (P ∘ snd) fs ->
        P <{ rec { fs } @ i }>.

    Hypothesis HHeader : forall fs b i,
        value b ->
        P b ->
        F.predfs_data (value ∘ snd) fs ->
        F.predfs_data (P ∘ snd) fs ->
        P <{ hdr { fs } valid:=b @ i }>.

    Hypothesis HError : forall err i, P <{ Error err @ i }>.

    Hypothesis HMatchkind : forall mk i, P <{ Matchkind mk @ i }>.

    Hypothesis HStack : forall fs hs n ni,
        Forall value hs ->
        Forall P hs ->
        P <{ Stack hs:fs[n] nextIndex:=ni }>.

    Definition custom_value_ind : forall (e : E.e tags_t),
        value e -> P e :=
      fix vind (e : E.e tags_t) (H : value e) : P e :=
        let fix lind {es : list (E.e tags_t)}
                (Hes : Forall value es) : Forall P es :=
            match Hes with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (lind Ht)
            end in
        let fix find {A : Type} {fs : F.fs tags_t (A * E.e tags_t)}
                (Hfs : F.predfs_data (value ∘ snd) fs) :
              F.predfs_data (P ∘ snd) fs :=
            match Hfs with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (find Ht)
            end in
        match H with
        | value_bool b i => HBool b i
        | value_bit w n i => HBit w n i
        | value_int w z i => HInt w z i
        | value_tuple _ i Hes => HTuple _ i Hes (lind Hes)
        | value_record _ i Hfs => HRecord _ i Hfs (find Hfs)
        | value_header _ _ i Hb Hfs => HHeader _ _ i
                                              Hb (vind _ Hb)
                                              Hfs (find Hfs)
        | value_error err i => HError err i
        | value_matchkind mk i => HMatchkind mk i
        | value_headerstack fs _ n ni Hhs => HStack
                                              fs _ n ni
                                              Hhs (lind Hhs)
        end.
  End IsValueInduction.
End IsValue.

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module F := P.F.
  Module PT := E.ProperType.

  Import P.P4cubNotations.
  Import Env.EnvNotations.

  Module V := IsValue.

  Section StepDefs.
    Import Typecheck.
    Import E.TypeEquivalence.
    Import F.FieldTactics.

    Ltac invert_Forall_cons :=
      match goal with
      | H: Forall _ (_ :: _) |- _ => inv H
      end.
    (**[]*)

    Context {tags_t : Type}.

    (** Expression environment. *)
    Definition eenv : Type := Env.t (name tags_t) (E.e tags_t).

    Definition eval_cast
               (target : E.t tags_t) (v : E.e tags_t) : option (E.e tags_t) :=
      match target, v with
      | {{ bit<xH> }}, <{ TRUE @ i }>         => Some (E.EBit 1%positive 1%N i)
      | {{ bit<xH> }}, <{ FALSE @ i }>        => Some (E.EBit 1%positive 0%N i)
      | {{ Bool }}, E.EBit 1%positive 1%N i => Some <{ TRUE @ i }>
      | {{ Bool }}, E.EBit 1%positive 0%N i => Some <{ FALSE @ i }>
      | {{ bit<w> }}, <{ _ S Z0 @ i }>       => Some <{ w W N0 @ i }>
      | {{ bit<w> }}, E.EInt _ (Zneg p) i
      | {{ bit<w> }}, E.EInt _ (Zpos p) i
        => let n := BitArith.return_bound w (Npos p) in
          Some <{ w W n @ i }>
      (* TODO: casting bit -> int is incorrect. *)
      | {{ int<w> }}, <{ _ W n @ i }>
        => let z := IntArith.return_bound w (Z.of_N n) in
          Some <{ w S z @ i }>
      | {{ bit<w> }}, <{ _ W n @ i }>
        => let n := BitArith.return_bound w n in
          Some <{ w W n @ i }>
      | {{ int<w> }}, <{ _ S z @ i}>
        => let z := IntArith.return_bound w z in
          Some <{ w S z @ i }>
      | _, _ => None
      end.
    (**[]*)

    Lemma eval_cast_types : forall errs Γ τ τ' v v',
        eval_cast τ' v = Some v' ->
        proper_cast τ' τ ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
    Proof.
      Hint Resolve BitArith.return_bound_bound : core.
      Hint Resolve IntArith.return_bound_bound : core.
      intros;
      match goal with
      | HPC: proper_cast _ _,
        HT : ⟦ _, _ ⟧ ⊢  _ ∈ _ |- _
        => inv HPC; inv HT; simpl in *; try discriminate
      end;
      try match goal with
          | H: match ?w with (_~1)%positive | _ => _ end = Some _
            |- _ => destruct w; inv H; try constructor; auto
          | H: (if ?b then _ else _) = Some _ |- _
            => destruct b; inv H; try constructor; auto
          | H: Some _ = Some _ |- _ => inv H; try constructor; auto
          end;
      try match goal with
          | n: N |- _ => destruct n;
            try match goal with
                | H: _ = Some _ |- _ => inv H; constructor; auto
                end
          end;
      try match goal with
          | z: Z |- _ => destruct z;
            try match goal with
                | H: _ = Some _ |- _ => inv H; constructor; auto
                end
          end;
      try match goal with
          | p: positive |- _ => destruct p;
           try match goal with
               | H: _ = Some _ |- _ => inv H; constructor; auto
               end
          end;
      try match goal with
          | |- BitArith.bound _ _
            => unfold BitArith.bound, BitArith.upper_bound; cbv; auto
          end.
    Qed.

    (** Unary Operations. *)
    Definition eval_uop (op : E.uop) (e : E.e tags_t) : option (E.e tags_t) :=
      match op, e with
      | E.Not, <{ BOOL b @ i }>
        => let b' := negb b in Some <{ BOOL b' @ i }>
      | E.BitNot, <{ w W n @ i }>
        => let n' := BitArith.neg w n in Some <{ w W n' @ i }>
      | E.UMinus, <{ w S z @ i }>
        => let z' := IntArith.neg w z in Some <{ w S z' @ i }>
      | _, _ => None
      end.
    (**[]*)

    (** Unsigned integer binary operations. *)
    Definition eval_bit_binop
               (op : E.bop) (w : positive)
               (n1 n2 : N) (i : tags_t) : option (E.e tags_t) :=
      match op with
      | E.Plus     => Some (E.EBit w (BitArith.plus_mod w n1 n2) i)
      | E.PlusSat  => Some (E.EBit w (BitArith.plus_sat w n1 n2) i)
      | E.Minus    => Some (E.EBit w (BitArith.minus_mod w n1 n2) i)
      | E.MinusSat => Some (E.EBit w (BitArith.return_bound w # N.sub n1 n2) i)
      | E.Shl      => Some (E.EBit w (BitArith.shift_left w n1 n2) i)
      | E.Shr      => Some (E.EBit w (BitArith.shift_right w n1 n2) i)
      | E.Le       => Some (E.EBool (N.leb n1 n2) i)
      | E.Ge       => Some (E.EBool (N.leb n2 n1) i)
      | E.Lt       => Some (E.EBool (N.ltb n1 n2) i)
      | E.Gt       => Some (E.EBool (N.ltb n2 n1) i)
      | E.Eq       => Some (E.EBool (N.eqb n1 n2) i)
      | E.NotEq    => Some (E.EBool (negb (N.eqb n1 n2)) i)
      | E.BitAnd   => Some (E.EBit w (BitArith.bit_and w n1 n2) i)
      | E.BitXor   => Some (E.EBit w (BitArith.bit_xor w n1 n2) i)
      | E.BitOr    => Some (E.EBit w (BitArith.bit_or  w n1 n2) i)
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    Lemma eval_bit_binop_numeric : forall errs Γ op w n1 n2 i v,
        numeric_bop op ->
        eval_bit_binop op w n1 n2 i = Some v ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ bit<w>.
    Proof.
      Hint Resolve BitArith.return_bound_bound : core.
      Hint Resolve BitArith.neg_bound : core.
      Hint Resolve BitArith.plus_mod_bound : core.
      Hint Extern 5 => unfold_bit_operation : core.
      Hint Extern 5 =>
      match goal with
      | |- context [_ # _ ] => unfold "#"
      end : core.
      intros;
      match goal with
      | H: numeric_bop _ |- _ => inv H; simpl in *
      end;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H; constructor
          end; auto.
    Qed.

    Lemma eval_bit_binop_comp : forall errs Γ op w n1 n2 i v,
        comp_bop op ->
        eval_bit_binop op w n1 n2 i = Some v ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ Bool.
    Proof.
      Hint Resolve BitArith.return_bound_bound : core.
      Hint Extern 5 => unfold_bit_operation : core.
      Hint Extern 5 =>
      match goal with
      | |- context [_ # _ ] => unfold "#"
      end : core.
      intros;
      match goal with
      | H: comp_bop _ |- _ => inv H; simpl in *
      end;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H; constructor
          end; auto.
    Qed.

    (** Signed integer binary operations. *)
    Definition eval_int_binop
               (op : E.bop) (w : positive)
               (z1 z2 : Z) (i : tags_t) : option (E.e tags_t) :=
      match op with
      | E.Plus     => Some # E.EInt w (IntArith.plus_mod w z1 z2) i
      | E.PlusSat  => Some # E.EInt w (IntArith.plus_sat w z1 z2) i
      | E.Minus    => Some # E.EInt w (IntArith.minus_mod w z1 z2) i
      | E.MinusSat => Some # E.EInt w (IntArith.minus_sat w z1 z2) i
      | E.Shl      => Some # E.EInt w (IntArith.shift_left w z1 z2) i
      | E.Shr      => Some # E.EInt w (IntArith.shift_right w z1 z2) i
      | E.Le       => Some # E.EBool (Z.leb z1 z2) i
      | E.Ge       => Some # E.EBool (Z.leb z2 z1) i
      | E.Lt       => Some # E.EBool (Z.ltb z1 z2) i
      | E.Gt       => Some # E.EBool (Z.ltb z2 z1) i
      | E.Eq       => Some # E.EBool (Z.eqb z1 z2) i
      | E.NotEq    => Some # E.EBool (negb (Z.eqb z1 z2)) i
      | E.BitAnd   => Some # E.EInt w (IntArith.bit_and w z1 z2) i
      | E.BitXor   => Some # E.EInt w (IntArith.bit_xor w z1 z2) i
      | E.BitOr    => Some # E.EInt w (IntArith.bit_or  w z1 z2) i
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    Lemma eval_int_binop_numeric : forall errs Γ op w n1 n2 i v,
        numeric_bop op ->
        eval_int_binop op w n1 n2 i = Some v ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ int<w>.
    Proof.
      Hint Resolve IntArith.return_bound_bound : core.
      Hint Extern 4 => unfold_int_operation : core.
      intros;
      match goal with
      | H: numeric_bop _ |- _ => inv H; simpl in *
      end; unfold "#" in *;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H; constructor
          end; auto.
    Qed.

    Lemma eval_int_binop_comp : forall errs Γ op w n1 n2 i v,
        comp_bop op ->
        eval_int_binop op w n1 n2 i = Some v ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ Bool.
    Proof.
      Hint Resolve IntArith.return_bound_bound : core.
      Hint Extern 5 => unfold_int_operation : core.
      intros;
      match goal with
      | H: comp_bop _ |- _ => inv H; simpl in *
      end; unfold "#" in *;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H; constructor
          end; auto.
    Qed.

    (** Boolean binary operations. *)
    Definition eval_bool_binop (op : E.bop) (b1 b2 : bool) : option bool :=
      match op with
      | E.Eq    => Some # eqb b1 b2
      | E.NotEq => Some # negb (eqb b1 b2)
      | E.And   => Some # b1 && b2
      | E.Or    => Some # b1 || b2
      | _       => None
      end.
    (**[]*)

    (** Equality operations. *)
    Definition eval_eq_binop (op : E.bop) (e1 e2 : E.e tags_t) : option bool :=
      match op with
      | E.Eq    => Some # E.ExprEquivalence.eqbe e1 e2
      | E.NotEq => Some # negb # E.ExprEquivalence.eqbe e1 e2
      | _       => None
      end.
    (**[]*)

    (** Binary operations. *)
    Definition eval_binop
               (op : E.bop) (e1 e2 : E.e tags_t)
               (i : tags_t) : option (E.e tags_t) :=
      match e1, e2 with
      | <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }>
        => option_map (fun b => <{ BOOL b @ i }>)
                     # eval_bool_binop op b1 b2
      | <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
        => if (w1 =? w2)%positive then
            eval_bit_binop op w1 n1 n2 i
          else
            match op with
            | E.PlusPlus
              => let w := (w1 + w2)%positive in
                let n := BitArith.bit_concat w1 w2 n1 n2 in
                Some <{ w W n @ i }>
            | _ => None
            end
      | <{ w1 S z1 @ _ }>, <{ w2 S z2 @ _ }>
        => if (w1 =? w2)%positive then
            eval_int_binop op w1 z1 z2 i
          else
            None
      | _, _ => option_map (fun b => <{ BOOL b @ i }>)
                          # eval_eq_binop op e1 e2
      end.
    (**[]*)

    (** Get header data from value. *)
    Definition header_data (v : E.e tags_t)
      : option (F.fs tags_t (E.t tags_t * E.e tags_t) * bool * tags_t * tags_t) :=
      match v with
      | <{ hdr { fs } valid:= BOOL b @ ib @ i}> => Some (fs,b,ib,i)
      | _ => None
      end.

    (** Get header stack data from value. *)
    Definition header_stack_data (v : E.e tags_t)
      : option (positive * N *
                F.fs tags_t (E.t tags_t) *
                (list (E.e tags_t))) :=
      match v with
      | <{ Stack hs:ts[n] nextIndex:=ni}> => Some (n,ni,ts,hs)
      | _ => None
      end.
    (**[]*)

    (** Header operations. *)
    Definition eval_hdr_op
               (op : E.hdr_op) (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
               (b : bool) (i ib : tags_t) : E.e tags_t :=
      match op with
      | E.HOIsValid => <{ BOOL b @ i}>
      | E.HOSetValid => <{ hdr { fs } valid:=TRUE @ ib @ i}>
      | E.HOSetInValid => <{ hdr { fs } valid:=FALSE @ ib @ i }>
      end.
    (**[]*)

    (** Default (value) Expression. *)
    Fixpoint edefault (i : tags_t) (τ : E.t tags_t) : E.e tags_t :=
      let fix lrec (ts : list (E.t tags_t)) : list (E.e tags_t) :=
          match ts with
          | []     => []
          | τ :: ts => edefault i τ :: lrec ts
          end in
      let fix frec (fs : F.fs tags_t (E.t tags_t))
          : F.fs tags_t (E.t tags_t * E.e tags_t) :=
          match fs with
          | [] => []
          | (x, τ) :: fs => (x, (τ, edefault i τ)) :: frec fs
          end in
      match τ with
      | {{ Bool }} => <{ BOOL false @ i }>
      | {{ bit<w> }} => E.EBit w 0%N i
      | {{ int<w> }} => E.EInt w 0%Z i
      | {{ error }} => <{ Error None @ i }>
      | {{ matchkind }} => <{ Matchkind exact @ i }>
      | {{ tuple ts }} => E.ETuple (lrec ts) i
      | {{ rec { fs } }} => E.ERecord (frec fs) i
      | {{ hdr { fs } }} => E.EHeader (frec fs) <{ BOOL false @ i }> i
      | {{ stack tfs[n] }}
          => let tefs := frec tfs in
            let hs :=
                repeat
                <{ hdr { tefs } valid:= BOOL false @ i @ i }>
                (Pos.to_nat n) in
            E.EHeaderStack tfs hs n 0%N
      end.
    (**[]*)

    Lemma value_edefault : forall i τ, V.value (edefault i τ).
    Proof.
      Hint Constructors V.value : core.
      intros; induction τ using E.custom_t_ind;
      simpl in *; auto; constructor; auto;
      try match goal with
          | |- Forall _ (repeat _ _) => apply repeat_Forall; constructor
          end;
      try match goal with
          | H: Forall _ ?ts |- _
            => induction ts as [| ? ? ?]; simpl in *; auto;
                try match goal with
                    | H: Forall _ (_ :: _) |- _ => inv H; auto
                    end
          end;
      try match goal with
          | H: F.predfs_data _ ?fs |- _
            => induction fs as [| [? ?] ? ?]; simpl in *;
              repeat constructor; try invert_cons_predfs;
              unfold F.predf_data, Basics.compose, F.predfs_data in *;
              simpl in *; auto
          end.
    Qed.

    Lemma default_types : forall errs Γ i τ,
        PT.proper_nesting τ ->
        let e := edefault i τ in
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ.
    Proof.
      Hint Resolve chk_bool : core.
      Hint Constructors PT.proper_nesting : core.
      Hint Rewrite repeat_length.
      Hint Resolve PT.proper_inside_header_nesting : core.
      simpl; intros; induction τ using E.custom_t_ind;
      simpl; econstructor; eauto;
      try match goal with
          | |- BitArith.bound ?w 0
            => unfold BitArith.bound;
              pose proof BitArith.upper_bound_ge_1 w; lia
          | |- IntArith.bound ?w 0
            => unfold IntArith.bound, IntArith.minZ, IntArith.maxZ;
              pose proof IntArith.upper_bound_ge_1 w; lia
          end;
      try match goal with
          | |- Forall _ (repeat _ _) => apply repeat_Forall; try apply chk_hdr_lit
          end;
      try match goal with
          | |- error_ok _ None => constructor
          end;
      try match goal with
          | H: PT.proper_nesting _ |- _ => inv H; intuition
              try match goal with
                  | H: PT.base_type {{ tuple _ }} |- _ => inv H
                  | H: PT.base_type {{ rec { _ } }} |- _ => inv H
                  | H: PT.base_type {{ hdr { _ } }} |- _ => inv H
                  | H: PT.base_type {{ stack _[_] }} |- _ => inv H
                  end
          end;
      try match goal with
          | IH: Forall _ ?ts |- Forall2 _ _ ?ts
            => induction ts; inv IH; try invert_Forall_cons;
              constructor; intuition
          end;
      try match goal with
          | IH: F.predfs_data _ ?fs |- F.relfs _ _ ?fs
            => induction fs as [| [? ?] ? ?]; constructor;
              unfold F.predfs_data,F.predf_data,
              F.relf,F.relfs,Basics.compose in *; simpl in *;
              repeat invert_Forall_cons; repeat constructor;
              try reflexivity; intuition
          end; simpl in *; auto; try lia;
        autorewrite with core; auto.
    Qed.

    (** Header stack operations. *)
    Definition eval_stk_op
               (i : tags_t) (op : E.hdr_stk_op)
               (size : positive) (nextIndex : N)
               (ts : F.fs tags_t (E.t tags_t))
               (hs : list (E.e tags_t))
      : option (E.e tags_t) :=
      let w := 32%positive in
      let sizenat := Pos.to_nat size in
      let hdefault :=
          E.EHeader
            (F.map (fun τ => (τ, edefault i τ)) ts)
          <{ BOOL false @ i }> i in
      match op with
      | E.HSOSize => let s := (Npos size)%N in Some <{ w W s @ i }>
      | E.HSONext => nth_error hs # N.to_nat nextIndex
      | E.HSOPush n
        => let nnat := N.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat hdefault nnat in
            let remains := firstn (sizenat - nnat) hs in
            let new_nextIndex := N.min (nextIndex + n) (N.pos size - 1)%N in
            Some (E.EHeaderStack ts (new_hdrs ++ remains) size new_nextIndex)
          else
            let new_hdrs := repeat hdefault sizenat in
            Some (E.EHeaderStack ts new_hdrs size ((N.pos size) - 1)%N)
      | E.HSOPop n
        => let nnat := N.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat hdefault nnat in
            let remains := skipn nnat hs in
            Some (E.EHeaderStack ts (remains ++ new_hdrs) size (nextIndex - n))
          else
            let new_hdrs := repeat hdefault sizenat in
            Some (E.EHeaderStack ts new_hdrs size 0%N)
      end.
    (**[]*)
  End StepDefs.

  Inductive expr_step {tags_t : Type} (ϵ : eenv)
    : E.e tags_t -> E.e tags_t -> Prop :=
  | step_var (x : name tags_t) (τ : E.t tags_t)
             (i : tags_t) (e : E.e tags_t) :
      ϵ x = Some e ->
      ℵ ϵ ** Var x:τ @ i -->  e
  | step_cast (τ : E.t tags_t) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Cast e:τ @ i -->  Cast e':τ @ i
  | step_cast_eval (τ : E.t tags_t) (v v' : E.e tags_t) (i : tags_t) :
      eval_cast τ v = Some v' ->
      V.value v ->
      ℵ ϵ ** Cast v:τ @ i -->  v'
  | step_uop (op : E.uop) (τ : E.t tags_t)
             (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** UOP op e:τ @ i -->  UOP op e':τ @ i
  | step_uop_eval (op : E.uop) (τ : E.t tags_t)
                  (v v' : E.e tags_t) (i : tags_t) :
      eval_uop op v = Some v' ->
      V.value v ->
      ℵ ϵ ** UOP op v:τ @ i -->  v'
  | step_bop_l (op : E.bop) (τl τr : E.t tags_t)
               (el el' er : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** el -->  el' ->
      ℵ ϵ ** BOP el:τl op er:τr @ i -->  BOP el':τl op er:τr @ i
  | step_bop_r (op : E.bop) (τl τr : E.t tags_t)
               (vl er er' : E.e tags_t) (i : tags_t) :
      V.value vl ->
      ℵ ϵ ** er -->  er' ->
      ℵ ϵ ** BOP vl:τl op er:τr @ i -->  BOP vl:τl op er':τr @ i
  | step_bop_eval (op : E.bop) (τl τr : E.t tags_t)
                  (vv vl vr : E.e tags_t) (i : tags_t) :
      eval_binop op vl vr i = Some vv ->
      V.value vl -> V.value vr ->
      ℵ ϵ ** BOP vl:τl op vr:τr @ i -->  vv
  | step_member (x : string tags_t) (τ : E.t tags_t)
                (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Mem e:τ dot x @ i -->  Mem e:τ dot x @ i
  | step_header_op (op : E.hdr_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** HDR_OP op e @ i -->  HDR_OP op e' @ i
  | step_header_op_eval (op : E.hdr_op) (v v' : E.e tags_t) (i : tags_t) :
      V.value v ->
      map_option (header_data v) (uncurry4 # eval_hdr_op op) = Some v' ->
      ℵ ϵ ** HDR_OP op v @ i -->  v'
  | step_stack_op (op : E.hdr_stk_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** STK_OP op e @ i -->  STK_OP op e' @ i
  | step_stack_op_eval (op : E.hdr_stk_op) (v v' : E.e tags_t) (i : tags_t) :
      V.value v ->
      bind_option (header_stack_data v) (uncurry4 # eval_stk_op i op) = Some v' ->
      ℵ ϵ ** STK_OP op v @ i -->  v'
  | step_stack_access (e e' : E.e tags_t) (n : N) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Access e[n] @ i -->  Access e'[n] @ i
  | step_tuple (prefix suffix : list (E.e tags_t))
               (e e' : E.e tags_t) (i : tags_t) :
      Forall V.value prefix ->
      ℵ ϵ ** e -->  e' ->
      let es := prefix ++ e :: suffix in
      let es' := prefix ++ e' :: suffix in
      ℵ ϵ ** tup es @ i -->  tup es' @ i
  | step_record (prefix suffix : F.fs tags_t (E.t tags_t * E.e tags_t))
                (x : string tags_t) (τ : E.t tags_t)
                (e e' : E.e tags_t) (i : tags_t) :
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ ** e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ ** rec { fs } @ i -->  rec { fs' } @ i
  | step_header (prefix suffix : F.fs tags_t (E.t tags_t * E.e tags_t))
                (x : string tags_t) (τ : E.t tags_t)
                (b e e' : E.e tags_t) (i : tags_t) :
      V.value b ->
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ ** e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ ** hdr { fs } valid:=b @ i -->  hdr { fs' } valid:=b @ i
  | step_header_valid (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
                      (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** hdr { fs } valid:=e @ i -->  hdr { fs } valid:=e' @ i
  | step_header_stack (ts : F.fs tags_t (E.t tags_t))
                      (prefix suffix : list (E.e tags_t))
                      (e e' : E.e tags_t) (size : positive)
                      (ni : N) (i : tags_t) :
      Forall V.value prefix ->
      ℵ ϵ ** e -->  e' ->
      let hs := prefix ++ e :: suffix in
      let hs' := prefix ++ e' :: suffix in
      ℵ ϵ ** Stack hs:ts[size] nextIndex:=ni -->  Stack hs':ts[size] nextIndex:=ni
  where "'ℵ' ϵ '**' e1 '-->' e2" := (expr_step ϵ e1 e2).
End Step.
*)
