Require Export Poulet4.P4cub.Check.
Require Export Poulet4.P4Arith.

Require Import Poulet4.P4cub.Value.

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.

Module V := Val.
Import V.ValueEquality.

(** Notation entries. *)
Declare Custom Entry p4evalsignal.

Reserved Notation "⟨ envn , e ⟩ ⇓ v"
         (at level 40, e custom p4expr, v custom p4value).

Reserved Notation "⧠ e ⇓ lv"
         (at level 40, e custom p4expr, lv custom p4lvalue).

Reserved Notation "⦑ envn , e ⦒ ⇓ st"
         (at level 40, e custom p4prsrexpr, st custom p4prsrstate).

Reserved Notation "⟪ cp , tenv , aenv , fenv , ienv , ϵ1 , s ⟫ ⤋ ⟪ ϵ2 , sig ⟫"
         (at level 40, s custom p4stmt,
          ϵ2 custom p4env, sig custom p4evalsignal).

Reserved Notation "⦉ ts1 , aa1 , fns , ins1 , ϵ1 , d ⦊ ⟱  ⦉ aa2 , ts2 ⦊"
         (at level 40, d custom p4ctrldecl, ts2 custom p4env, ts1 custom p4env).

Reserved Notation "⦇ cs1 , fns1 , ins1 , ϵ1 , d ⦈ ⟱  ⦇ ins2 , fns2 , cs2 ⦈"
         (at level 40, d custom p4topdecl).

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module ST := P.Stmt.
  Module PS := P.Parser.ParserState.
  Module CD := P.Control.ControlDecl.
  Module TP := P.TopDecl.
  Module F := P.F.

  Import P.P4cubNotations.
  Import V.ValueNotations.
  Import V.LValueNotations.

  (** Statement signals. *)
  Inductive signal : Type :=
  | SIG_Cont                  (* continue *)
  | SIG_Exit                  (* exit *)
  | SIG_Rtrn (v : option V.v) (* return *).

  Notation "x"
    := x (in custom p4evalsignal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4evalsignal at level 0).
  Notation "'X'" := SIG_Exit (in custom p4evalsignal at level 0).
  Notation "'R' 'of' v ?"
    := (SIG_Rtrn v) (in custom p4evalsignal at level 0).
  Notation "'Void'" := (SIG_Rtrn None) (in custom p4evalsignal at level 0).
  Notation "'Fruit' v" := (SIG_Rtrn (Some v)) (in custom p4evalsignal at level 0).

  Import Env.EnvNotations.

  Section StepDefs.
    (** Bit-slicing. *)
    Definition eval_slice (hi lo : positive) (v : V.v) : option V.v :=
      match v with
      | ~{ _ VW z }~
      | ~{ _ VS z }~
        => let w' := (hi - lo + 1)%positive in
        Some $ V.VBit w' $
             BitArith.mod_bound w' $
             BitArith.bitstring_slice z hi lo
      | _ => None
      end.
    (**[]*)

    (** Unary Operations. *)
    Definition eval_uop (op : E.uop) (v : V.v) : option V.v :=
      match op, v with
      | _{ ! }_, ~{ VBOOL b }~ => Some $ V.VBool  $ negb b
      | _{ ~ }_, ~{ w VW n }~  => Some $ V.VBit w $ BitArith.bit_not w n
      | _{ ~ }_, ~{ w VS n }~  => Some $ V.VInt w $ IntArith.bit_not w n
      | _{ - }_, ~{ w VW z }~  => Some $ V.VBit w $ BitArith.neg w z
      | _{ - }_, ~{ w VS z }~  => Some $ V.VInt w $ IntArith.neg w z
      | _{ isValid }_, ~{ HDR { _ } VALID:=b }~ => Some ~{ VBOOL b }~
      | _{ setValid }_, ~{ HDR { vs } VALID:=_ }~
        => Some ~{ HDR { vs } VALID:=true }~
      | _{ setInValid }_, ~{ HDR { vs } VALID:=_ }~
        => Some ~{ HDR { vs } VALID:=false }~
      | _{ Size }_, ~{ STACK _:_[n] NEXT:=_ }~ => Some $ V.VBit 32%positive $ Zpos n
      | _{ Next }_, ~{ STACK hs:_[_] NEXT:=ni }~
        => bvs <<| nth_error hs $ Z.to_nat ni ;;
          match bvs with
          | (b,vs) => ~{ HDR { vs } VALID:=b }~
          end
      | _{ Push n }_, ~{ STACK hs:ts[size] NEXT:=ni }~
        => let nnat := Pos.to_nat n in
          let sizenat := Pos.to_nat size in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat (false, F.map V.vdefault ts) nnat in
            let remains := firstn (sizenat - nnat) hs in
            let new_nextIndex := Z.min (ni + Z.pos n) (Z.pos size - 1)%Z in
            Some $ V.VHeaderStack ts (new_hdrs ++ remains) size new_nextIndex
          else
            let new_hdrs := repeat (false, F.map V.vdefault ts) sizenat in
            Some $ V.VHeaderStack ts new_hdrs size ((Z.pos size) - 1)%Z
      | _{ Pop n }_, ~{ STACK hs:ts[size] NEXT:=ni }~
        => let nnat := Pos.to_nat n in
          let sizenat := Pos.to_nat size in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat (false, F.map V.vdefault ts) nnat in
            let remains := skipn nnat hs in
            Some $
                 V.VHeaderStack ts (remains ++ new_hdrs) size $
                 Z.max 0%Z (ni - Zpos n)%Z
          else
            let new_hdrs := repeat (false, F.map V.vdefault ts) sizenat in
            Some $ V.VHeaderStack ts new_hdrs size 0%Z
      | _, _ => None
      end.
    (**[]*)

    (** Binary operations. *)
    Definition eval_bop (op : E.bop) (v1 v2 : V.v) : option V.v :=
      match op, v1, v2 with
      | +{ + }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.plus_mod w n1 n2
      | +{ + }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.plus_mod w z1 z2
      | +{ |+| }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.plus_sat w n1 n2
      | +{ |+| }+,  ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.plus_sat w z1 z2
      | +{ - }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.minus_mod w n1 n2
      | +{ - }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.minus_mod w z1 z2
      | +{ |-| }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.minus_sat w n1 n2
      | +{ |-| }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.minus_sat w z1 z2
      | +{ × }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.mult_mod w n1 n2
      | +{ × }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.mult_mod w z1 z2
      | +{ << }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.shift_left w n1 n2
      | +{ << }+, ~{ w VS z1 }~, ~{ _ VW z2 }~
        => Some $ V.VInt w $ IntArith.shift_left w z1 z2
      | +{ >> }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.shift_right w n1 n2
      | +{ >> }+, ~{ w VS z1 }~, ~{ _ VW z2 }~
        => Some $ V.VInt w $ IntArith.shift_right w z1 z2
      | +{ & }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.bit_and w n1 n2
      | +{ & }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.bit_and w z1 z2
      | +{ ^ }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.bit_xor w n1 n2
      | +{ ^ }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.bit_xor w z1 z2
      | +{ | }+, ~{ w VW n1 }~, ~{ _ VW n2 }~
        => Some $ V.VBit w $ BitArith.bit_or w n1 n2
      | +{ | }+, ~{ w VS z1 }~, ~{ _ VS z2 }~
        => Some $ V.VInt w $ IntArith.bit_or w z1 z2
      | +{ <= }+, ~{ w VW n1 }~, ~{ _ VW n2 }~ => Some $ V.VBool (n1 <=? n2)%Z
      | +{ <= }+, ~{ w VS z1 }~, ~{ _ VS z2 }~ => Some $ V.VBool (z1 <=? z2)%Z
      | +{ < }+, ~{ w VW n1 }~, ~{ _ VW n2 }~ => Some $ V.VBool (n1 <? n2)%Z
      | +{ < }+, ~{ w VS z1 }~, ~{ _ VS z2 }~ => Some $ V.VBool (z1 <? z2)%Z
      | +{ >= }+, ~{ w VW n1 }~, ~{ _ VW n2 }~ => Some $ V.VBool (n2 <=? n1)%Z
      | +{ >= }+, ~{ w VS z1 }~, ~{ _ VS z2 }~ => Some $ V.VBool (z2 <=? z1)%Z
      | +{ > }+, ~{ w VW n1 }~, ~{ _ VW n2 }~ => Some $ V.VBool (n2 <? n1)%Z
      | +{ > }+, ~{ w VS z1 }~, ~{ _ VS z2 }~ => Some $ V.VBool (z2 <? z1)%Z
      | +{ && }+, ~{ VBOOL b1 }~, ~{ VBOOL b2 }~ => Some $ V.VBool (b1 && b2)
      | +{ || }+, ~{ VBOOL b1 }~, ~{ VBOOL b2 }~ => Some $ V.VBool (b1 || b2)
      | +{ == }+, _, _ => Some $ V.VBool $ eqbv v1 v2
      | +{ != }+, _, _ => Some $ V.VBool $ negb $ eqbv v1 v2
      | +{ ++ }+, ~{ w1 VW n1 }~, ~{ w2 VW n2 }~
      | +{ ++ }+, ~{ w1 VW n1 }~, ~{ w2 VS n2 }~
        => Some $ V.VBit (w1 + w2)%positive $ BitArith.concat w1 w2 n1 n2
      | +{ ++ }+, ~{ w1 VS n1 }~, ~{ w2 VS n2 }~
      | +{ ++ }+, ~{ w1 VS n1 }~, ~{ w2 VW n2 }~
        => Some $ V.VInt (w1 + w2)%positive $ IntArith.concat w1 w2 n1 n2
      | _, _, _ => None
      end.
    (**[]*)

    Definition eval_cast
               (target : E.t) (v : V.v) : option V.v :=
      match target, v with
      | {{ bit<xH> }}, ~{ TRUE }~         => Some (V.VBit 1%positive 1%N)
      | {{ bit<xH> }}, ~{ FALSE }~        => Some (V.VBit 1%positive 0%N)
      | {{ Bool }}, V.VBit 1%positive 1%N => Some ~{ TRUE }~
      | {{ Bool }}, V.VBit 1%positive 0%N => Some ~{ FALSE }~
      | {{ bit<w> }}, ~{ _ VS z }~ => let n := BitArith.mod_bound w z in
                                     Some ~{ w VW n }~
      | {{ int<w> }}, ~{ _ VW n }~ => let z := IntArith.mod_bound w n in
                                     Some ~{ w VS z }~
      | {{ bit<w> }}, ~{ _ VW n }~ => let n := BitArith.mod_bound w n in
                                     Some ~{ w VW n }~
      | {{ int<w> }}, ~{ _ VS z }~ => let z := IntArith.mod_bound w z in
                                     Some ~{ w VS z }~
      | {{ rec { fs } }}, ~{ TUPLE vs }~
        => Some $ V.VRecord $ combine (F.keys fs) vs
      | {{ hdr { fs } }}, ~{ TUPLE vs }~
        => Some $ V.VHeader (combine (F.keys fs) vs) true
      | _, _ => None
      end.
    (**[]*)

    Definition eval_member (x : string) (v : V.v) : option V.v :=
      match v with
      | ~{ REC { vs } }~
      | ~{ HDR { vs } VALID:=_ }~ => F.get x vs
      | _ => None
      end.
    (**[]*)

    Section Lemmas.
      Import Typecheck.
      Import V.ValueTyping.
      Import P4ArithTactics.
      Import E.ProperType.

      Section HelpersType.
        Local Hint Constructors type_value : core.

        Lemma eval_member_types : forall errs x v v' ts τ τ',
            eval_member x v = Some v' ->
            member_type ts τ ->
            F.get x ts = Some τ' ->
            ∇ errs ⊢ v ∈ τ ->
            ∇ errs ⊢ v' ∈ τ'.
        Proof.
          intros errs x v v' ts τ τ' Heval Hmem Hget Ht;
          inv Hmem; inv Ht; unravel in *.
          - eapply F.relfs_get_r in H1 as [? ?]; eauto.
            intuition. rewrite Heval in H0; inv H0; eauto.
          - eapply F.relfs_get_r in H2 as [? ?]; eauto.
            intuition. rewrite Heval in H1; inv H1; eauto.
        Qed.

        Local Hint Extern 0 => bit_bounded : core.
        Local Hint Extern 0 => int_bounded : core.

        Lemma eval_slice_types : forall errs v v' τ hi lo w,
            eval_slice hi lo v = Some v' ->
            (lo <= hi < w)%positive ->
            numeric_width w τ ->
            ∇ errs ⊢ v ∈ τ ->
            let w' := (hi - lo + 1)%positive in
            ∇ errs ⊢ v' ∈ bit<w'>.
        Proof.
          intros errs v v' τ hi lo w Heval Hw Hnum Hv w'; subst w'.
          inv Hnum; inv Hv; unravel in *; inv Heval; auto 2.
        Qed.

        Lemma eval_bop_type : forall errs op τ1 τ2 τ v1 v2 v,
            bop_type op τ1 τ2 τ -> eval_bop op v1 v2 = Some v ->
            ∇ errs ⊢ v1 ∈ τ1 -> ∇ errs ⊢ v2 ∈ τ2 -> ∇ errs ⊢ v ∈ τ.
        Proof.
          intros errs op τ1 τ2 τ v1 v2 v Hbop Heval Ht1 Ht2; inv Hbop;
          repeat match goal with
                 | H: Some _ = Some _ |- _ => inv H; constructor; auto 2
                 | H: numeric _ |- _ => inv H
                 | H: numeric_width _ _ |- _ => inv H
                 | |- _ => inv Ht1; inv Ht2; unravel in *
                 | |- BitArith.bound _ _ => unfold_bit_operation; auto 2
                 | |- IntArith.bound _ _ => unfold_int_operation; auto 2
                 end; auto 2.
        Qed.

        Local Hint Resolve proper_inside_header_nesting : core.

        Lemma eval_cast_types : forall errs v v' τ τ',
            proper_cast τ τ' -> eval_cast τ' v = Some v' ->
            ∇ errs ⊢ v ∈ τ -> ∇ errs ⊢ v' ∈ τ'.
        Proof.
          intros errs v v' τ τ' Hpc Heval Ht; inv Hpc; inv Ht;
            unravel in *; try match goal with
                              | H: Some _ = Some _ |- _ => inv H
                              end; auto 2.
          - destruct b; inv Heval; constructor; cbv; auto 2.
          - destruct n; inv Heval; auto 1; destruct p; inv H0; auto 1.
          - destruct w; inv Heval; auto 2.
          - destruct w2; inv Heval; auto 2.
          - constructor. generalize dependent fs.
            induction vs as [| v vs IHvs]; intros [| [x τ] fs] H;
            inv H; unravel; constructor; unfold F.relf in *;
            unravel; try apply IHvs; auto 2.
          - constructor; unfold F.values,F.value in *.
            + apply pn_header; rewrite F.predfs_data_map; auto 1.
            + clear H0. generalize dependent fs.
              induction vs as [| v vs IHvs];
              intros [| [x τ] fs] H; inv H; constructor;
              try split; unravel; try apply IHvs; auto 2.
        Qed.

        Local Hint Constructors proper_nesting : core.
        Hint Rewrite repeat_length.
        Hint Rewrite app_length.
        Hint Rewrite firstn_length.
        Hint Rewrite skipn_length.
        Hint Rewrite Forall_app.
        Hint Rewrite @F.map_snd.
        Hint Rewrite @map_compose.
        Hint Rewrite (@Forall2_map_l E.t).
        Hint Rewrite (@Forall2_Forall E.t).
        Hint Rewrite @F.predfs_data_map.
        Hint Rewrite @F.relfs_split_map_iff.
        Hint Rewrite @F.map_fst.
        Local Hint Resolve Forall_impl : core.
        Local Hint Resolve vdefault_types : core.
        Local Hint Resolve Forall_firstn : core.
        Local Hint Resolve Forall_skipn : core.

        Lemma eval_uop_types : forall errs op τ τ' v v',
            uop_type op τ τ' -> eval_uop op v = Some v' ->
            ∇ errs ⊢ v ∈ τ -> ∇ errs ⊢ v' ∈ τ'.
        Proof.
          intros errs op τ τ' v v' Huop Heval Ht;
          inv Huop; inv Ht; unravel in *; inv Heval; auto 2;
          invert_proper_nesting;
          repeat match goal with
                 | H: Some _ = Some _ |- _ => inv H
                 | H: (if ?b then _ else _) = _ |- _ => destruct b as [? | ?]
                 end; try constructor; try (destruct n; lia); auto 2;
          autorewrite with core; try split; auto 2;
          try (apply repeat_Forall; simpl; constructor; auto 2;
               autorewrite with core in *; split; [intuition | eauto 5]).
          - destruct (nth_error hs (Z.to_nat ni))
              as [[b vs] |] eqn:equack; inv H0; constructor; auto 2;
            apply (Forall_nth_error _ hs (Z.to_nat ni) (b, vs)) in H6; inv H6; auto 1.
        Qed.
      End HelpersType.

      Section HelpersExist.
        Lemma eval_slice_exists : forall errs v τ hi lo w,
          (lo <= hi < w)%positive ->
          numeric_width w τ ->
          ∇ errs ⊢ v ∈ τ ->
          exists v', eval_slice hi lo v = Some v'.
        Proof.
          intros errs v τ hi lo w Hw Hnum Hv;
          inv Hnum; inv Hv; unravel; eauto 2.
        Qed.

        Lemma eval_bop_exists : forall errs op τ1 τ2 τ v1 v2,
            bop_type op τ1 τ2 τ ->
            ∇ errs ⊢ v1 ∈ τ1 -> ∇ errs ⊢ v2 ∈ τ2 ->
            exists v, eval_bop op v1 v2 = Some v.
        Proof.
          intros errs op τ1 τ2 τ v1 v2 Hbop Ht1 Ht2; inv Hbop;
          repeat inv_numeric; inv Ht1; inv Ht2; unravel; eauto 2;
          try inv_numeric_width.
        Qed.

        Lemma eval_cast_exists : forall errs τ τ' v,
            proper_cast τ τ' -> ∇ errs ⊢ v ∈ τ -> exists v', eval_cast τ' v = Some v'.
        Proof.
          intros errs τ τ' v Hpc Ht; inv Hpc; inv Ht; unravel; eauto 2.
          - destruct b; eauto 2.
          - destruct n; eauto 2; destruct p; eauto 2;
            try (cbv in *; destruct H1; try destruct p; discriminate).
          - destruct w; eauto 2.
          - destruct w2; eauto 2.
        Qed.

        Lemma eval_uop_exist : forall errs op τ τ' v,
            uop_type op τ τ' -> ∇ errs ⊢ v ∈ τ -> exists v', eval_uop op v = Some v'.
        Proof.
          intros errs op τ τ' v Huop Ht; inv Huop; inv Ht;
          unravel; repeat inv_numeric; eauto 2;
          try (destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2).
          - assert (Hnith : (Z.to_nat ni < length hs)%nat) by lia;
            pose proof nth_error_exists _ _ Hnith as [[b vs] Hexists];
            rewrite Hexists; eauto 2.
        Qed.

        Lemma eval_member_exists : forall errs x v ts τ τ',
            member_type ts τ ->
            F.get x ts = Some τ' ->
            ∇ errs ⊢ v ∈ τ ->
            exists v', eval_member x v = Some v'.
        Proof.
          intros errs x v ts τ τ' Hmem Hget Ht;
          inv Hmem; inv Ht; unravel.
          - eapply F.relfs_get_r in H1 as [? ?]; eauto 2;
            intuition; eauto 2.
          - eapply F.relfs_get_r in H2 as [? ?]; eauto 2;
            intuition; eauto 2.
      Qed.
      End HelpersExist.
    End Lemmas.

    (** Variable to Value mappings. *)
    Definition epsilon : Type := Env.t string V.v.

    (** Lookup an lvalue. *)
    Fixpoint lv_lookup (ϵ : epsilon) (lv : V.lv) : option V.v :=
      match lv with
      | l{ VAR x }l => ϵ x
      | l{ lv DOT x }l =>
        (* TODO: use monadic bind. *)
        match lv_lookup ϵ lv with
        | None => None
        | Some ~{ REC { fs } }~
        | Some ~{ HDR { fs } VALID:=_ }~ => F.get x fs
        | Some _ => None
        end
      | l{ lv[n] }l =>
        match lv_lookup ϵ lv with
        | None => None
        | Some ~{ STACK vss:_[_] NEXT:=_ }~ =>
          match nth_error vss (Z.to_nat n) with
          | None => None
          | Some (b,vs) => Some ~{ HDR { vs } VALID:=b }~
          end
        | Some _ => None
        end
      end.
    (**[]*)

    (** Updating an lvalue in an environment. *)
    Fixpoint lv_update (lv : V.lv) (v : V.v) (ϵ : epsilon) : epsilon :=
      match lv with
      | l{ VAR x }l    => !{ x ↦ v ;; ϵ }!
      | l{ lv DOT x }l =>
        match lv_lookup ϵ lv with
        | Some ~{ REC { vs } }~ => lv_update lv (V.VRecord (F.update x v vs)) ϵ
        | Some ~{ HDR { vs } VALID:=b }~ =>
          lv_update lv (V.VHeader (F.update x v vs) b) ϵ
        | Some _ | None => ϵ
        end
      | l{ lv[n] }l =>
        match v, lv_lookup ϵ lv with
        | ~{ HDR { vs } VALID:=b }~ ,
          Some ~{ STACK vss:ts[size] NEXT:=ni }~ =>
          let vss := nth_update (Z.to_nat n) (b,vs) vss in
          lv_update lv ~{ STACK vss:ts[size] NEXT:=ni }~ ϵ
        | _, Some _ | _, None => ϵ
        end
      end.
    (**[]*)

    (** Create a new environment
        from a closure environment where
        values of [In] args are substituted
        into the function parameters. *)
    Definition copy_in
               (argsv : V.argsv)
               (ϵcall : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn v     => !{ x ↦ v ;; ϵ }!
                | P.PAInOut lv => match lv_lookup ϵcall lv with
                                 | None   => ϵ
                                 | Some v => !{ x ↦ v ;; ϵ }!
                                end
                | P.PAOut _    => ϵ
                end) argsv.
    (**[]*)

    (** Update call-site environment with
        out variables from function call evaluation. *)
    Definition copy_out
               (argsv : V.argsv)
               (ϵf : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn _ => ϵ
                | P.PAOut lv
                | P.PAInOut lv =>
                  match ϵf x with
                  | None   => ϵ
                  | Some v => lv_update lv v ϵ
                  end
                end) argsv.
    (**[]*)

    (** Evidence that control-flow
        is interrupted by an exit or return statement. *)
    Inductive interrupt : signal -> Prop :=
    | interrupt_exit : interrupt SIG_Exit
    | interrupt_rtrn (vo : option V.v) : interrupt (SIG_Rtrn vo).
    (**[]*)

    Context {tags_t : Type}.

    (** Table environment. *)
    Definition tenv : Type := Env.t string (CD.table tags_t).

    (** Function declarations and closures. *)
    Inductive fdecl : Type :=
    | FDecl (closure : epsilon) (fs : fenv) (ins : ienv) (body : ST.s tags_t)
    with fenv : Type :=
    | FEnv (fs : Env.t string fdecl)
    (** Action declarations and closures *)
    with adecl : Type :=
    | ADecl (closure : epsilon) (fs : fenv) (ins : ienv) (aa : aenv) (body : ST.s tags_t)
    with aenv : Type :=
    | AEnv (aa : Env.t string adecl)
    (** Instances and Environment. *)
    with inst : Type :=
    | CInst (closure : epsilon) (fs : fenv) (ins : ienv)
            (tbls : tenv) (aa : aenv)
            (apply_blk : ST.s tags_t)  (* control instance *)
    | PInst (* TODO: parser instance *)
    | EInst (* TODO: extern object instance *)
    with ienv : Type :=
    | IEnv (ins : Env.t string inst).
    (**[]*)

    (** Function lookup. *)
    Definition lookup '(FEnv fs : fenv) : string -> option fdecl := fs.

    (** Bind a function declaration to an environment. *)
    Definition update '(FEnv fs : fenv) (x : string) (d : fdecl) : fenv :=
      FEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Instance lookup. *)
    Definition ilookup '(IEnv fs : ienv) : string -> option inst := fs.

    (** Bind an instance to an environment. *)
    Definition iupdate '(IEnv fs : ienv) (x : string) (d : inst) : ienv :=
      IEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Action lookup. *)
    Definition alookup '(AEnv aa : aenv) : string -> option adecl := aa.

    (** Bind a function declaration to an environment. *)
    Definition aupdate '(AEnv aa : aenv) (x : string) (d : adecl) : aenv :=
      AEnv !{ x ↦ d ;; aa }!.
    (**[]*)

    (** Control plane table entries,
        essentially mapping tables to an action call. *)
    Definition entries : Type :=
      list (V.v * E.matchkind) ->
      list string ->
      string * E.args tags_t.
    (**[]*)

    (** Control plane tables. *)
    Definition ctrl : Type := Env.t string entries.

    (** Control declarations and closures. *)
    Inductive cdecl : Type :=
    | CDecl (cs : cenv) (closure : epsilon) (fs : fenv) (ins : ienv)
            (body : CD.d tags_t) (apply_block : ST.s tags_t)
    with cenv : Type :=
    | CEnv (cs : Env.t string cdecl).
    (**[]*)

    (** Control lookup. *)
    Definition clookup '(CEnv cs : cenv) : string -> option cdecl := cs.

    (** Bind an instance to an environment. *)
    Definition cupdate '(CEnv cs : cenv) (x : string) (d : cdecl) : cenv :=
      CEnv !{ x ↦ d ;; cs }!.
    (**[]*)
  End StepDefs.

  (** Expression big-step semantics. *)
  Inductive expr_big_step {tags_t : Type} (ϵ : epsilon) : E.e tags_t -> V.v -> Prop :=
  (* Literals. *)
  | ebs_bool (b : bool) (i : tags_t) :
      ⟨ ϵ, BOOL b @ i ⟩ ⇓ VBOOL b
  | ebs_bit (w : positive) (n : Z) (i : tags_t) :
      ⟨ ϵ, w W n @ i ⟩ ⇓ w VW n
  | ebs_int (w : positive) (z : Z) (i : tags_t) :
      ⟨ ϵ, w S z @ i ⟩ ⇓ w VS z
  | ebs_var (x : string) (τ : E.t) (i : tags_t) (v : V.v) :
      ϵ x = Some v ->
      ⟨ ϵ, Var x:τ @ i ⟩ ⇓ v
  | ebs_slice (e : E.e tags_t) (τ : E.t) (hi lo : positive)
              (i : tags_t) (v' v : V.v) :
      eval_slice hi lo v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Slice e:τ [hi:lo] @ i ⟩ ⇓ v'
  | ebs_cast (τ : E.t) (e : E.e tags_t) (i : tags_t) (v v' : V.v) :
      eval_cast τ v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Cast e:τ @ i ⟩ ⇓ v'
  | ebs_error (err : option string) (i : tags_t) :
      ⟨ ϵ, Error err @ i ⟩ ⇓ ERROR err
  | ebs_matchkind (mk : E.matchkind) (i : tags_t) :
      ⟨ ϵ, Matchkind mk @ i ⟩ ⇓ MATCHKIND mk
  (* Unary Operations. *)
  | ebs_uop (op : E.uop) (τ : E.t) (e : E.e tags_t) (i : tags_t) (v v' : V.v) :
      eval_uop op v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, UOP op e:τ @ i ⟩ ⇓ v'
  (* Binary Operations. *)
  | ebs_bop (op : E.bop) (τ1 τ2 : E.t) (e1 e2 : E.e tags_t)
            (i : tags_t) (v v1 v2 : V.v) :
      eval_bop op v1 v2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      ⟨ ϵ, BOP e1:τ1 op e2:τ2 @ i ⟩ ⇓ v
  (* Structs *)
  | ebs_mem (e : E.e tags_t) (x : string) (τ : E.t)
            (i : tags_t) (v v' : V.v) :
      eval_member x v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Mem e:τ dot x @ i ⟩ ⇓ v'
  | ebs_tuple (es : list (E.e tags_t)) (i : tags_t)
              (vs : list (V.v)) :
      Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
      ⟨ ϵ, tup es @ i ⟩ ⇓ TUPLE vs
  | ebs_rec_lit (efs : F.fs string (E.t * E.e tags_t))
                (i : tags_t) (vfs : F.fs string V.v) :
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, rec { efs } @ i ⟩ ⇓ REC { vfs }
  | ebs_hdr_lit (efs : F.fs string (E.t * E.e tags_t))
                (e : E.e tags_t) (i : tags_t) (b : bool)
                (vfs : F.fs string V.v) :
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
      ⟨ ϵ, hdr { efs } valid:=e @ i ⟩ ⇓ HDR { vfs } VALID:=b
  | ebs_hdr_stack (ts : F.fs string (E.t))
                  (hs : list (E.e tags_t))
                  (n : positive) (ni : Z) (i : tags_t)
                  (vss : list (bool * F.fs string (V.v))) :
      Forall2
        (fun e bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
        hs vss ->
      ⟨ ϵ, Stack hs:ts[n] nextIndex:=ni @ i ⟩ ⇓ STACK vss:ts [n] NEXT:=ni
  | ebs_access (e : E.e tags_t) (i : tags_t)
               (n : positive) (index ni : Z)
               (ts : F.fs string (E.t))
               (vss : list (bool * F.fs string (V.v)))
               (b : bool) (vs : F.fs string (V.v)) :
      nth_error vss (Z.to_nat index) = Some (b,vs) ->
      ⟨ ϵ, e ⟩ ⇓ STACK vss:ts [n] NEXT:=ni ->
      ⟨ ϵ, Access e[index] @ i ⟩ ⇓ HDR { vs } VALID:=b
  where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
  (**[]*)

  (** A custom induction principle for
      the expression big-step relation. *)
  Section ExprEvalInduction.
    Variable (tags_t: Type).

    Variable P : epsilon -> E.e tags_t -> V.v -> Prop.

    Hypothesis HBool : forall ϵ b i, P ϵ <{ BOOL b @ i }> ~{ VBOOL b }~.

    Hypothesis HBit : forall ϵ w n i, P ϵ <{ w W n @ i }> ~{ w VW n }~.

    Hypothesis HInt : forall ϵ w z i, P ϵ <{ w S z @ i }> ~{ w VS z }~.

    Hypothesis HVar : forall ϵ x τ i v,
        ϵ x = Some v ->
        P ϵ <{ Var x:τ @ i }> v.
    (**[]*)

    Hypothesis HSlice : forall ϵ e τ hi lo i v v',
        eval_slice hi lo v = Some v' ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        P ϵ e v ->
        P ϵ <{ Slice e:τ [hi:lo] @ i }> v'.
    (**[]*)

    Hypothesis HCast : forall ϵ τ e i v v',
        eval_cast τ v = Some v' ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        P ϵ e v ->
        P ϵ <{ Cast e:τ @ i }> v'.
    (**[]*)

    Hypothesis HError : forall ϵ err i, P ϵ <{ Error err @ i }> ~{ ERROR err }~.

    Hypothesis HMatchkind : forall ϵ mk i,
        P ϵ <{ Matchkind mk @ i }> ~{ MATCHKIND mk }~.
    (**[]*)

    Hypothesis HUop : forall ϵ op τ e i v v',
        eval_uop op v = Some v' ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        P ϵ e v ->
        P ϵ <{ UOP op e:τ @ i }> v'.

    Hypothesis HBop : forall ϵ op τ1 τ2 e1 e2 i v v1 v2,
        eval_bop op v1 v2 = Some v ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        P ϵ e1 v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        P ϵ e2 v2 ->
        P ϵ <{ BOP e1:τ1 op e2:τ2 @ i }> v.
    (**[]*)

    Hypothesis HMem : forall ϵ e x τ i v v',
        eval_member x v = Some v' ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        P ϵ e v ->
        P ϵ <{ Mem e:τ dot x @ i }> v'.
    (**[]*)

    Hypothesis HTuple : forall ϵ es i vs,
        Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
        Forall2 (P ϵ) es vs ->
        P ϵ <{ tup es @ i }> ~{ TUPLE vs }~.
    (**[]*)

    Hypothesis HRecLit : forall ϵ efs i vfs,
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
        P ϵ <{ rec { efs } @ i }> ~{ REC { vfs } }~.
    (**[]*)

    Hypothesis HHdrLit : forall ϵ efs e i b vfs,
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        P ϵ e ~{ VBOOL b }~ ->
        P ϵ <{ hdr { efs } valid:=e @ i }> ~{ HDR { vfs } VALID:=b }~.
    (**[]*)

    Hypothesis HHdrStack : forall ϵ ts hs n ni i vss,
        Forall2
          (fun e bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
          hs vss ->
        Forall2
          (fun e bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             P ϵ e ~{ HDR { vs } VALID:=b}~ )
          hs vss ->
        P ϵ <{ Stack hs:ts[n] nextIndex:=ni @ i }> ~{ STACK vss:ts[n] NEXT:=ni }~.
    (**[]*)

    Hypothesis HAccess : forall ϵ e i n index ni ts vss b vs,
        nth_error vss (Z.to_nat index) = Some (b,vs) ->
        ⟨ ϵ, e ⟩ ⇓ STACK vss:ts[n] NEXT:=ni ->
        P ϵ e ~{ STACK vss:ts[n] NEXT:=ni }~ ->
        P ϵ <{ Access e[index] @ i }> ~{ HDR { vs } VALID:=b }~.
    (**[]*)

    (** Custom induction principle for
        the expression big-step relation.
        [Do induction ?H using custom_expr_big_step_ind]. *)
    Definition custom_expr_big_step_ind :
      forall (ϵ : epsilon) (e : E.e tags_t)
        (v : V.v) (Hy : ⟨ ϵ, e ⟩ ⇓ v), P ϵ e v :=
      fix ebsind ϵ e v Hy :=
        let fix lind
                {es : list (E.e tags_t)}
                {vs : list (V.v)}
                (HR : Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs)
            : Forall2 (P ϵ) es vs :=
            match HR with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hh Ht
              => Forall2_cons _ _ (ebsind _ _ _ Hh) (lind Ht)
            end in
        let fix fsind
                {efs : F.fs string (E.t * E.e tags_t)}
                {vfs : F.fs string (V.v)}
                (HRs : F.relfs
                         (fun te v =>
                            let e := snd te in
                            ⟨ ϵ , e ⟩ ⇓ v) efs vfs)
                : F.relfs
                    (fun te v => let e := snd te in P ϵ e v)
                    efs vfs :=
                match HRs with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons _ _ (conj Hx Hhd) Htl
                  => Forall2_cons _ _ (conj Hx (ebsind _ _ _ Hhd)) (fsind Htl)
                end in
        let fix ffind
                {es : list (E.e tags_t)}
                {vss : list (bool * F.fs string (V.v))}
                (HRs : Forall2
                         (fun e bvs =>
                            let b := fst bvs in
                            let vs := snd bvs in
                            ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
                         es vss)
            : Forall2
                (fun e bvs =>
                   let b := fst bvs in
                   let vs := snd bvs in
                   P ϵ e ~{ HDR { vs } VALID:=b}~ )
                es vss :=
            match HRs with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hhead Htail
              => Forall2_cons _ _ (ebsind _ _ _ Hhead) (ffind Htail)
            end in
        match Hy with
        | ebs_bool _ b i => HBool ϵ b i
        | ebs_bit _ w n i => HBit ϵ w n i
        | ebs_int _ w z i => HInt ϵ w z i
        | ebs_var _ _ τ i _ Hx => HVar _ _ τ i _ Hx
        | ebs_slice _ _ _ _ _ i _ _ Hv He
          => HSlice _ _ _ _ _ i _ _ Hv He (ebsind _ _ _ He)
        | ebs_cast _ _ _ i _ _ Hv He
          => HCast _ _ _ i _ _ Hv He (ebsind _ _ _ He)
        | ebs_error _ err i => HError _ err i
        | ebs_matchkind _ mk i => HMatchkind _ mk i
        | ebs_uop _ _ _ _ i _ _ Hv He
          => HUop _ _ _ _ i _ _ Hv He (ebsind _ _ _ He)
        | ebs_bop _ _ _ _ _ _ i _ _ _ Hv He1 He2
          => HBop _ _ _ _ _ _ i _ _ _ Hv He1 (ebsind _ _ _ He1) He2 (ebsind _ _ _ He2)
        | ebs_mem _ _ _ _ i _ _ Heval He
          => HMem _ _ _ _ i _ _ Heval He (ebsind _ _ _ He)
        | ebs_tuple _ _ i _ HR => HTuple _ _ i _ HR (lind HR)
        | ebs_rec_lit _ _ i _ HR => HRecLit _ _ i _ HR (fsind HR)
        | ebs_hdr_lit _ _ _ i _ _ HR He
          => HHdrLit _ _ _ i _ _ HR (fsind HR) He (ebsind _ _ _ He)
        | ebs_hdr_stack _ _ _ n ni i _ HR
          => HHdrStack _ _ _ n ni i _ HR (ffind HR)
        | ebs_access _ _ i n index ni ts _ _ _ Hnth He
          => HAccess _ _ i n index ni ts _ _ _ Hnth He (ebsind _ _ _ He)
        end.
    (**[]*)

  End ExprEvalInduction.

  Inductive lvalue_big_step {tags_t : Type} : E.e tags_t -> V.lv -> Prop :=
  | lvbs_var (x : string) (τ : E.t) (i : tags_t) :
      ⧠ Var x:τ @ i ⇓ VAR x
  | lvbs_member (e : E.e tags_t) (x : string)
                (τ : E.t) (i : tags_t) (lv : V.lv) :
      ⧠ e ⇓ lv ->
      ⧠ Mem e:τ dot x @ i ⇓ lv DOT x
  | lvbs_access (e : E.e tags_t) (i : tags_t)
                      (lv : V.lv) (n : Z) :
      let w := 32%positive in
      ⧠ e ⇓ lv ->
      ⧠ Access e[n] @ i ⇓ lv[n]
  where "⧠ e ⇓ lv" := (lvalue_big_step e lv).
  (**[]*)

  (** Parser-expression evaluation. *)
  Inductive parser_expr_big_step
            {tags_t} (ϵ : epsilon) : PS.e tags_t -> PS.state -> Prop :=
  | pebs_goto (st : PS.state) (i : tags_t) :
      ⦑ ϵ, goto st @ i ⦒ ⇓ st
  | pebs_select (e : E.e tags_t) (def : PS.e tags_t)
                (cases : F.fs (E.e tags_t) (PS.e tags_t))
                (i : tags_t) (v : V.v) (st_def : PS.state)
                (vcases : F.fs V.v PS.state) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      Forall2
        (fun epe vps =>
           let e := fst epe in
           let v := fst vps in
           let pe := snd epe in
           let ps := snd vps in
           ⦑ ϵ, pe ⦒ ⇓ ps /\ ⟨ ϵ, e ⟩ ⇓ v)
        cases vcases ->
      ⦑ ϵ, def ⦒ ⇓ st_def ->
      let st := match F.get v vcases with
                | None => st_def
                | Some st => st
                end in
      ⦑ ϵ, select e { cases } default:=def @ i ⦒ ⇓ st
  where "⦑ envn , e ⦒ ⇓ st"
          := (parser_expr_big_step envn e st).
  (**[]*)

  Section ParserExprInduction.
    Variable tags_t : Type.
    Variable P : epsilon -> PS.e tags_t -> PS.state -> Prop.

    Hypothesis HGoto : forall ϵ st i,
      P ϵ p{ goto st @ i }p st.

    Hypothesis HSelect : forall ϵ e def cases i v
                           st_def vcases,
      ⟨ ϵ, e ⟩ ⇓ v ->
      Forall2
        (fun epe vps =>
           let e := fst epe in
           let v := fst vps in
           let pe := snd epe in
           let ps := snd vps in
           ⦑ ϵ, pe ⦒ ⇓ ps /\ ⟨ ϵ, e ⟩ ⇓ v)
        cases vcases ->
      Forall2 (fun epe vps =>
                 let pe := snd epe in
                 let ps := snd vps in
                 P ϵ pe ps) cases vcases ->
      ⦑ ϵ, def ⦒ ⇓ st_def ->
      P ϵ def st_def ->
      let st := match F.get v vcases with
                | None => st_def
                | Some st => st
                end in
      P ϵ p{ select e { cases } default:=def @ i }p st.

    Definition custom_parser_expr_big_step_ind :
      forall (ϵ : epsilon) (e : PS.e tags_t) (st : PS.state),
        ⦑ ϵ, e ⦒ ⇓ st -> P ϵ e st :=
      fix pebsind ϵ e st H :=
        let fix cases_ind
                {cases : F.fs (E.e tags_t) (PS.e tags_t)}
                {vcases : F.fs V.v PS.state}
                (Hcases :
                   Forall2
                     (fun epe vps =>
                        let e := fst epe in
                        let v := fst vps in
                        let pe := snd epe in
                        let ps := snd vps in
                        ⦑ ϵ, pe ⦒ ⇓ ps /\ ⟨ ϵ, e ⟩ ⇓ v)
                     cases vcases)
            : Forall2
                (fun epe vps =>
                   let pe := snd epe in
                   let ps := snd vps in
                   P ϵ pe ps) cases vcases :=
            match Hcases with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ (conj Hcase _) Htail
              => Forall2_cons _ _ (pebsind _ _ _ Hcase) (cases_ind Htail)
            end in
        match H with
        | pebs_goto _ st i => HGoto _ st i
        | pebs_select _ _ _ _ i _ _ _ He Hcases Hdef
          => HSelect _ _ _ _ i _ _ _ He
                    Hcases (cases_ind Hcases)
                    Hdef (pebsind _ _ _ Hdef)
        end.
    (**[]*)
  End ParserExprInduction.

  (** Statement big-step semantics. *)
  Inductive stmt_big_step
            {tags_t : Type} (cp : ctrl) (ts : tenv) (aa : aenv)
            (fs : fenv) (ins : ienv) (ϵ : epsilon) :
    ST.s tags_t -> epsilon -> signal -> Prop :=
  | sbs_skip (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, skip @ i ⟫ ⤋ ⟪ ϵ, C ⟫
  | sbs_seq_cont (s1 s2 : ST.s tags_t) (i : tags_t)
                 (ϵ' ϵ'' : epsilon) (sig : signal) :
      ⟪ cp, ts, aa, fs, ins, ϵ,  s1 ⟫ ⤋ ⟪ ϵ',  C ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ', s2 ⟫ ⤋ ⟪ ϵ'', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ,  s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ'', sig ⟫
  | sbs_seq_interrupt (s1 s2 : ST.s tags_t) (i : tags_t)
                         (ϵ' : epsilon) (sig : signal) :
      interrupt sig ->
      ⟪ cp, ts, aa, fs, ins, ϵ, s1 ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ', sig ⟫
  | sbs_block_cont (s : ST.s tags_t) (ϵ' : epsilon) :
      ⟪ cp, ts, aa, fs, ins, ϵ, s ⟫ ⤋ ⟪ ϵ', C ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, b{ s }b ⟫ ⤋ ⟪ ϵ ≪ ϵ', C ⟫
  | sbs_block_interrupt (s : ST.s tags_t) (ϵ' : epsilon) (sig : signal) :
      interrupt sig ->
      ⟪ cp, ts, aa, fs, ins, ϵ, s ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, b{ s }b ⟫ ⤋ ⟪ ϵ ≪ ϵ', sig ⟫
  | sbs_vardecl (τ : E.t) (x : string)
                (i : tags_t) (v : V.v) :
      V.vdefault τ = v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, var x : τ @ i ⟫ ⤋ ⟪ x ↦ v ;; ϵ, C ⟫
  | sbs_assign (τ : E.t) (e1 e2 : E.e tags_t) (i : tags_t)
               (lv : V.lv) (v : V.v) (ϵ' : epsilon) :
      lv_update lv v ϵ = ϵ' ->
      ⧠ e1 ⇓ lv ->
      ⟨ ϵ, e2 ⟩ ⇓ v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, asgn e1 := e2 : τ @ i ⟫ ⤋ ⟪ ϵ', C ⟫
  | sbs_exit (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, exit @ i ⟫ ⤋ ⟪ ϵ, X ⟫
  | sbs_retvoid (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, returns @ i ⟫ ⤋ ⟪ ϵ, Void ⟫
  | sbs_retfruit (τ : E.t) (e : E.e tags_t)
                 (i : tags_t) (v : V.v) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, return e:τ @ i ⟫ ⤋ ⟪ ϵ, Fruit v ⟫
  | sbs_cond_true (guard : E.e tags_t)
                  (tru fls : ST.s tags_t) (i : tags_t)
                  (ϵ' : epsilon) (sig : signal) :
      ⟨ ϵ, guard ⟩ ⇓ TRUE ->
      ⟪ cp, ts, aa, fs, ins, ϵ, tru ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig ⟫
  | sbs_cond_false (guard : E.e tags_t)
                   (tru fls : ST.s tags_t) (i : tags_t)
                   (ϵ' : epsilon) (sig : signal) :
      ⟨ ϵ, guard ⟩ ⇓ FALSE ->
      ⟪ cp, ts, aa, fs, ins, ϵ, fls ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig ⟫
  | sbs_action_call (args : E.args tags_t)
                    (argsv : V.argsv)
                    (a : string) (i : tags_t)
                    (body : ST.s tags_t) (aclosure : aenv)
                    (fclosure : fenv) (ains : ienv)
                    (closure ϵ' ϵ'' ϵ''' : epsilon) :
      (* Looking up action. *)
      alookup aa a = Some (ADecl closure fclosure ains aclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Action evaluation *)
      ⟪ cp, ts, aclosure, fclosure, ains, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, calling a with args @ i ⟫ ⤋ ⟪ ϵ''', C ⟫
  | sbs_void_call (args : E.args tags_t)
                  (argsv : V.argsv)
                  (f : string) (i : tags_t)
                  (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                  (closure ϵ' ϵ'' ϵ''' : epsilon) :
      (* Looking up function. *)
      lookup fs f = Some (FDecl closure fclosure fins body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Function evaluation *)
      ⟪ cp, ts, aa, fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, call f with args @ i ⟫ ⤋ ⟪ ϵ''', C ⟫
  | sbs_fruit_call (args : E.args tags_t)
                   (argsv : V.argsv)
                   (f : string) (τ : E.t)
                   (e : E.e tags_t) (i : tags_t)
                   (v : V.v) (lv : V.lv)
                   (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                   (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
      (* Looking up function. *)
      lookup fs f = Some (FDecl closure fclosure fins body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Lvalue Evaluation. *)
      ⧠ e ⇓ lv ->
      (* Function evaluation. *)
      ⟪ cp, ts, aa, fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Fruit v ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      (* Assignment to lvalue. *)
      lv_update lv v ϵ''' = ϵ'''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, let e:τ := call f with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
  | sbs_apply (args : E.args tags_t)
              (argsv : V.argsv)
              (x : string) (i : tags_t)
              (body : ST.s tags_t) (fclosure : fenv) (iins : ienv)
              (tblclosure : tenv) (aclosure : aenv)
              (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
      (* Instance lookup. *)
      ilookup ins x = Some (CInst closure fclosure iins tblclosure aclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Apply block evaluation. *)
      ⟪ cp, tblclosure, aclosure, fclosure, iins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, apply x with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
  | sbs_invoke (x : string) (i : tags_t)
               (es : entries)
               (ky : list (E.t * E.e tags_t * E.matchkind))
               (acts : list (string))
               (vky : list (V.v * E.matchkind))
               (a : string) (args : E.args tags_t)
               (ϵ' : epsilon)
               (sig : signal) :
      cp x = Some es ->
      ts x = Some (CD.Table ky acts) ->
      Forall2 (fun '(_,k,_) '(v,_) => ⟨ ϵ, k ⟩ ⇓ v) ky vky ->
      (* Black box, need extra assumption for soundness *)
      es vky acts = (a,args) ->
      ⟪ cp, ts, aa, fs, ins, ϵ, calling a with args @ i ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, invoke x @ i ⟫ ⤋ ⟪ ϵ', sig ⟫
  where "⟪ cp , ts , aa , fs , ins , ϵ , s ⟫ ⤋ ⟪ ϵ' , sig ⟫"
          := (stmt_big_step cp ts aa fs ins ϵ s ϵ' sig).

  (** Control declaration big-step semantics. *)
  Inductive ctrldecl_big_step
            {tags_t : Type} (tbls : tenv) (aa : aenv)
            (fns : fenv) (ins : ienv) (ϵ : epsilon)
    : CD.d tags_t -> aenv -> tenv -> Prop :=
  | cdbs_action (a : string) (params : E.params)
                (body : ST.s tags_t) (i : tags_t) :
      let aa' := aupdate aa a (ADecl ϵ fns ins aa body) in
      ⦉ tbls, aa, fns, ins, ϵ, action a (params) {body} @ i ⦊
        ⟱  ⦉ aa', tbls ⦊
  | cdbs_table (t : string)
               (kys : list
                        (E.t * E.e tags_t * E.matchkind))
               (actns : list (string))
               (i : tags_t) :
      let tbl := CD.Table kys actns in
      ⦉ tbls, aa, fns, ins, ϵ, table t key:=kys actions:=actns @ i ⦊
        ⟱  ⦉ aa, t ↦ tbl;; tbls ⦊
  | cdbs_seq (d1 d2 : CD.d tags_t) (i : tags_t)
             (aa' aa'' : aenv) (tbls' tbls'' : tenv) :
      ⦉ tbls,  aa,  fns, ins, ϵ, d1 ⦊ ⟱  ⦉ aa',  tbls'  ⦊ ->
      ⦉ tbls', aa', fns, ins, ϵ, d2 ⦊ ⟱  ⦉ aa'', tbls'' ⦊ ->
      ⦉ tbls,  aa,  fns, ins, ϵ, d1 ;c; d2 @ i ⦊
        ⟱  ⦉ aa'', tbls'' ⦊
  where "⦉ ts1 , aa1 , fns , ins1 , ϵ1 , d ⦊ ⟱  ⦉ aa2 , ts2 ⦊"
          := (ctrldecl_big_step ts1 aa1 fns ins1 ϵ1 d aa2 ts2).
  (**[]*)

  (** Top-level declaration big-step semantics. *)
  Inductive topdecl_big_step
            {tags_t : Type} (cs : cenv)
            (fns : fenv) (ins : ienv) (ϵ : epsilon)
    : TP.d tags_t -> ienv -> fenv -> cenv -> Prop :=
  | dbs_instantiate (c : string) (x : string)
                    (cargs : E.constructor_args tags_t)
                    (vargs : F.fs string (either (V.v) inst)) (i : tags_t)
                    (ctrlclosure : cenv) (fclosure : fenv)
                    (iclosure ins' : ienv)
                    (body : CD.d tags_t) (applyblk : ST.s tags_t)
                    (closure ϵ' ϵ'' : epsilon) (tbls : tenv) (aa : aenv) :
      clookup cs c = Some (CDecl ctrlclosure closure fclosure iclosure body applyblk) ->
      F.relfs
        (fun carg v =>
           match carg,v with
           | E.CAExpr e, Left v => ⟨ ϵ, e ⟩ ⇓ v
           | E.CAName c, Right cinst => ilookup ins c = Some cinst
           | _, _ => False
           end) cargs vargs ->
      F.fold (fun x v '(ϵ,ins) =>
                match v with
                | Left v => (!{ x ↦ v;; ϵ }!, ins)
                | Right cinst => (ϵ, iupdate ins x cinst)
                end) vargs (closure,iclosure) = (ϵ',ins') ->
      let ae := AEnv !{ ∅ }! in
      ⦉ ∅, ae, fclosure, ins', ϵ', body ⦊ ⟱  ⦉ aa, tbls ⦊ ->
      let ins'' := iupdate ins x (CInst ϵ'' fclosure ins' tbls aa applyblk) in
      ⦇ cs, fns, ins, ϵ, Instance x of c(cargs) @ i ⦈ ⟱  ⦇ ins'', fns, cs ⦈
  | tpbs_control (c : string) (cparams : E.constructor_params)
                 (params : E.params) (body : CD.d tags_t)
                 (apply_blk : ST.s tags_t) (i : tags_t) (cs' : @cenv tags_t) :
      let cs' := cupdate cs c (CDecl cs ϵ fns ins body apply_blk) in
      ⦇ cs, fns, ins, ϵ,
        control c (cparams)(params) apply { apply_blk } where { body } @ i ⦈
        ⟱  ⦇ ins, fns, cs' ⦈
  | tpbs_fruit_function (f : string) (params : E.params)
                        (τ : E.t) (body : ST.s tags_t) (i : tags_t) :
      let fns' := update fns f (FDecl ϵ fns ins body) in
      ⦇ cs, fns, ins, ϵ, fn f (params) -> τ { body } @ i ⦈
        ⟱  ⦇ ins, fns', cs ⦈
  | tpbs_void_function (f : string) (params : E.params)
                       (body : ST.s tags_t) (i : tags_t) :
      let fns' := update fns f (FDecl ϵ fns ins body) in
      ⦇ cs, fns, ins, ϵ, void f (params) { body } @ i ⦈
        ⟱  ⦇ ins, fns', cs ⦈
  | tpbs_seq (d1 d2 : TP.d tags_t) (i : tags_t)
             (ins' ins'' : ienv) (fns' fns'' : fenv) (cs' cs'' : cenv) :
      ⦇ cs,  fns,  ins,  ϵ, d1 ⦈ ⟱  ⦇ ins',  fns',  cs'  ⦈ ->
      ⦇ cs', fns', ins', ϵ, d2 ⦈ ⟱  ⦇ ins'', fns'', cs'' ⦈ ->
      ⦇ cs,  fns,  ins,  ϵ, d1 ;%; d2 @ i ⦈ ⟱  ⦇ ins'', fns'', cs'' ⦈
  where "⦇ cs1 , fns1 , ins1 , ϵ1 , d ⦈ ⟱  ⦇ ins2 , fns2 , cs2 ⦈"
          := (topdecl_big_step cs1 fns1 ins1 ϵ1 d ins2 fns2 cs2).
  (**[]*)
End Step.
