Require Export Coq.Classes.EquivDec.
Require Export Coq.PArith.BinPosDef.
Export Pos.
Require Export P4light.AST.
Require Export P4light.P4Arith.

(** * Environments *)

(** Note how the type of the environment's domain
    is an argument to the environment functor. *)
Module Env.

  (** Definition of environments. *)
  Definition t (D T : Type) : Type := D -> option T.

  (** The empty environment. *)
  Definition empty (D T : Type) : t D T := fun _ => None.

  Section EnvDefs.
    Context {D T : Type}.

    Context {equiv_rel : D -> D -> Prop}.

    Context {HEquiv : Equivalence equiv_rel}.

    Context {HE : EqDec D equiv_rel}.

    (** Updating the environment. *)
    Definition bind (x : D) (v : T) (e : t D T) : t D T :=
      fun y => if x == y then Some v else e y.

    (* TODO: whatever lemmas needed. *)
  End EnvDefs.

  Module EnvNotations.
    Declare Custom Entry p4env.

    Notation "'!{' env '}!'" := env (env custom p4env at level 99).
    Notation "x" := x (in custom p4env at level 0, x constr at level 0).
    Notation "x ↦ v ';;' e"
      := (bind x v e)
           (in custom p4env at level 40, e custom p4env,
               right associativity).
  End EnvNotations.
End Env.

(** * Typechecking *)
Module Typecheck.
  Module P := P4light.

  Module E := P.Expr.
  Module ST := P.Stmt.
  Module D := P.Decl.
  Module F := P.F.
  Definition dir := P.Dir.d.

  Import E.TypeNotations.
  Import E.ExprNotations.

  (** Statement signals. *)
  Inductive signal : Set :=
  | SIG_Cont   (* continue *)
  | SIG_Return (* return *).

  (** Least-upper bound on signals *)
  Definition lub (sg1 sg2 : signal) : signal :=
    match sg1, sg2 with
    | SIG_Cont, _
    | _, SIG_Cont => SIG_Cont
    | _, _        => SIG_Return
    end.
  (**[]*)

  Declare Custom Entry p4signal.

  Notation "x"
    := x (in custom p4signal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4signal at level 0).
  Notation "'R'" := SIG_Return (in custom p4signal at level 0).

  Reserved Notation "⟦ ers ',' mks ',' gm ⟧ ⊢ e ∈ t"
           (at level 40, e custom p4expr, t custom p4type at level 0).

  Import Env.EnvNotations.

  Reserved Notation "⦃ fe ',' errs ',' mks ',' g1 ⦄ ⊢ s ⊣ g2 ',' sg"
           (at level 40, s custom p4stmt,
            g2 custom p4env, sg custom p4signal).

  Section TypeCheck.
    Variable (tags_t : Type).

    (** Available matchkinds. *)
    Definition matchkinds : Type := Env.t (string tags_t) unit.

    (** Available error names. *)
    Definition errors : Type := Env.t (string tags_t) unit.

    (** Typing context. *)
    Definition gam : Type := Env.t (name tags_t) (E.t tags_t).

    Definition bare (x : string tags_t) : name tags_t :=
      Typed.BareName x.
    (**[]*)

    Instance P4NameEquivalence : Equivalence (equivn tags_t) :=
      NameEquivalence tags_t.
    (**[]*)

    Instance P4NameEqDec : EqDec (name tags_t) (equivn tags_t) :=
      NameEqDec tags_t.
    (**[]*)

    Definition out_update
               (fs : F.fs tags_t (dir * (E.t tags_t * E.e tags_t))) : gam -> gam :=
      fs
        ▷ F.filter (fun '(d,_) =>
                      match d with
                      | P.Dir.DOut | P.Dir.DInOut => true
                      | _ => false end)
        ▷ F.fold (fun x '(_, (τ,_)) Γ =>
                    let x' := bare x in
                    !{ x' ↦ τ ;; Γ }!).

    (** Evidence for a type being numeric. *)
    Inductive numeric : E.t tags_t -> Prop :=
    | numeric_bit (w : positive) : numeric {{ bit<w> }}
    | numeric_int (w : positive) : numeric {{ int<w> }}.

    (** Evidence for a type being a numeric of a given width. *)
    Inductive numeric_width (w : positive) : E.t tags_t -> Prop :=
    | numeric_width_bit : numeric_width w {{ bit<w> }}
    | numeric_width_int : numeric_width w {{ int<w> }}.

    (** Evidence that a binary operation is purely numeric. *)
    Inductive numeric_bop : E.bop -> Prop :=
    | numeric_bop_plus : numeric_bop E.Plus
    | numeric_bop_plussat : numeric_bop E.PlusSat
    | numeric_bop_minus : numeric_bop E.Minus
    | numeric_bop_minussat : numeric_bop E.MinusSat
    | numeric_bop_shl : numeric_bop E.Shl
    | numeric_bop_shr : numeric_bop E.Shr
    | numeric_bop_bitand : numeric_bop E.BitAnd
    | numeric_bop_bitxor : numeric_bop E.BitXor
    | numeric_bop_bitor : numeric_bop E.BitOr.

    (** Evidence a binary operator gives a bool from numbers. *)
    Inductive comp_bop : E.bop -> Prop :=
    | comp_bop_le : comp_bop E.Le
    | comp_bop_ge : comp_bop E.Ge
    | comp_bop_lt : comp_bop E.Lt
    | comp_bop_gt : comp_bop E.Gt.

    (** Evidence a binary operator is purely boolean. *)
    Inductive bool_bop : E.bop -> Prop :=
    | bool_bop_and : bool_bop E.And
    | bool_bop_or  : bool_bop E.Or.

    (** Expression typing as a relation. *)
    Inductive check
              (errs : errors) (mkds : matchkinds)
              (Γ : gam) : E.e tags_t -> E.t tags_t -> Prop :=
    (* Literals. *)
    | chk_bool (b : bool) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ BOOL b @ i ∈ Bool
    | chk_bit (w : positive) (n : N) (i : tags_t) :
        BitArith.bound w n ->
        ⟦ errs , mkds , Γ ⟧ ⊢ w W n @ i ∈ bit<w>
    | chk_int (w : positive) (n : Z) (i : tags_t) :
        IntArith.bound w n ->
        ⟦ errs , mkds , Γ ⟧ ⊢ w S n @ i ∈ int<w>
    | chk_var (x : name tags_t) (τ : E.t tags_t) (i : tags_t) :
        Γ x = Some τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Var x :: τ @ i end ∈ τ
    (* Unary operations. *)
    | chk_not (e : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ Bool ->
        ⟦ errs , mkds , Γ ⟧ ⊢ ! e :: Bool @ i end ∈ Bool
    | chk_bitnot (w : positive) (e : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ bit<w> ->
        ⟦ errs , mkds , Γ ⟧ ⊢ ~ e :: bit<w> @ i end ∈ bit<w>
    | chk_uminus (w : positive) (e : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ int<w> ->
        ⟦ errs , mkds , Γ ⟧ ⊢ - e :: int<w> @ i end ∈ int<w>
    (* Binary Operations. *)
    | chk_numeric_bop (op : E.bop) (τ τ' : E.t tags_t)
                      (e1 e2 : E.e tags_t) (i : tags_t) :
        E.equivt τ τ' -> numeric τ -> numeric_bop op ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ' ->
        check errs mkds Γ (E.EBop op τ τ' e1 e2 i) τ
    | chk_comp_bop (op : E.bop) (τ τ' : E.t tags_t)
                   (e1 e2 : E.e tags_t) (i : tags_t) :
        E.equivt τ τ' -> numeric τ -> comp_bop op ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ' ->
        check errs mkds Γ (E.EBop op τ τ' e1 e2 i) {{ Bool }}
    | chk_bool_bop (op : E.bop) (e1 e2 : E.e tags_t) (i : tags_t) :
        bool_bop op ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ Bool ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ Bool ->
        check errs mkds Γ (E.EBop op {{ Bool }} {{ Bool }} e1 e2 i) {{ Bool }}
    | chk_eq (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ == e1 :: τ e2 :: τ @ i end ∈ Bool
    | chk_neq (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ != e1 :: τ e2 :: τ @ i end ∈ Bool
    | chk_plusplus_bit (τ : E.t tags_t) (m n w : positive)
                       (e1 e2 : E.e tags_t) (i : tags_t) :
        (m + n)%positive = w ->
        numeric_width n τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<m> ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ ++ e1 :: bit<m> e2 :: τ @ i end ∈ bit<w>
    (* Member expressions. *)
    | chk_hdr_mem (e : E.e tags_t) (x : string tags_t)
                  (fields : F.fs tags_t (E.t tags_t))
                  (τ : E.t tags_t) (i : tags_t) :
        In (x, τ) fields ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ hdr { fields } ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Mem e :: hdr { fields } dot x @ i end ∈ τ
    | chk_rec_mem (e : E.e tags_t) (x : string tags_t)
                  (fields : F.fs tags_t (E.t tags_t))
                  (τ : E.t tags_t) (i : tags_t) :
        In (x, τ) fields ->
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ rec { fields } ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Mem e :: rec { fields } dot x @ i end ∈ τ
    (* Structs. *)
    | chk_rec_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (tfs : F.fs tags_t (E.t tags_t)) (i : tags_t) :
        F.relfs
          (fun te τ =>
             E.equivt (fst te) τ /\
             let e := snd te in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
        ⟦ errs , mkds , Γ ⟧ ⊢ rec { efs } @ i ∈ rec { tfs }
    | chk_hdr_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (tfs : F.fs tags_t (E.t tags_t)) (i : tags_t) :
        F.relfs
          (fun te τ =>
             E.equivt (fst te) τ /\
             let e := snd te in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
        ⟦ errs , mkds , Γ ⟧ ⊢ hdr { efs } @ i ∈ hdr { tfs }
    (* Errors and matchkinds. *)
    | chk_error (err : string tags_t) (i : tags_t) :
        errs err = Some tt ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Error err @ i ∈ error
    | chk_matchkind (mkd : string tags_t) (i : tags_t) :
        mkds mkd = Some tt ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Matchkind mkd @ i ∈ matchkind
    where "⟦ ers ',' mks ',' gm ⟧ ⊢ e ∈ ty"
            := (check ers mks gm e ty).
    (**[]*)

    Import ST.StmtNotations.

    (** Available functions. *)
    Definition fenv : Type := Env.t (name tags_t) (E.arrowT tags_t).

    Inductive check_stmt
              (fns : fenv) (errs : errors)
              (mkds : matchkinds)
              (Γ : gam) : ST.s tags_t -> gam -> signal -> Prop :=
    | chk_skip (i : tags_t) :
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ skip @ i ⊣ Γ, C
    | chk_seq_cont (s1 s2 : ST.s tags_t) (Γ' Γ'' : gam)
                   (i : tags_t) (sig : signal) :
        (⦃ fns , errs , mkds , Γ  ⦄ ⊢ s1 ⊣ Γ', C) ->
        (⦃ fns , errs , mkds , Γ' ⦄ ⊢ s2 ⊣ Γ'', sig) ->
        (⦃ fns , errs , mkds , Γ  ⦄ ⊢ s1 ; s2 @ i ⊣ Γ'', sig)
    | chk_seq_ret (s1 s2 : ST.s tags_t) (Γ' : gam) (i : tags_t) :
        (⦃ fns , errs , mkds , Γ ⦄ ⊢ s1 ⊣ Γ', R) ->
        (⦃ fns , errs , mkds , Γ ⦄ ⊢ s1 ; s2 @ i ⊣ Γ', R)
    | chk_assign (τ : E.t tags_t) (x : name tags_t)
                 (e : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ asgn x := e :: τ @ i fin ⊣ x ↦ τ ;; Γ, C
    | chk_cond (guard : E.e tags_t) (tru fls : ST.s tags_t)
               (Γ1 Γ2 : gam) (i : tags_t) (sgt sgf sg : signal) :
        lub sgt sgf = sg ->
        ⟦ errs , mkds , Γ ⟧ ⊢ guard ∈ Bool ->
        (⦃ fns , errs , mkds , Γ ⦄ ⊢ tru ⊣ Γ1, sgt) ->
        (⦃ fns , errs , mkds , Γ ⦄ ⊢ fls ⊣ Γ2, sgf) ->
        ⦃ fns , errs , mkds , Γ ⦄
          ⊢ if guard :: Bool then tru else fls @ i fin ⊣ Γ, sg
    | chk_return_void (i : tags_t) :
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ returns @ i ⊣ Γ, R
    | chk_return_fruit (τ : E.t tags_t) (e : E.e tags_t) (i : tags_t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ ->
        (⦃ fns , errs, mkds , Γ ⦄ ⊢ return e :: τ @ i fin ⊣ Γ, R)
    | chk_exit (i : tags_t) :
        ⦃ fns, errs, mkds , Γ ⦄ ⊢ exit @ i ⊣ Γ, R
    | chk_method_call (Γ' : gam) (params : F.fs tags_t (dir * E.t tags_t))
                      (args : F.fs tags_t (dir * (E.t tags_t * E.e tags_t)))
                      (f : name tags_t) (i : tags_t) :
        out_update args Γ = Γ' ->
        fns f = Some (E.Arrow params None) ->
        F.relfs
          (fun dte dt =>
             fst dt = fst dte /\ E.equivt (snd dt) (dte ▷ snd ▷ fst) /\
             let e := dte ▷ snd ▷ snd in
             let τ := snd dt in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ) args params ->
        (⦃ fns , errs , mkds , Γ ⦄ ⊢ call f with args @ i fin ⊣ Γ', C)
    | chk_call (Γ' : gam) (params : F.fs tags_t (dir * E.t tags_t))
               (τ : E.t tags_t)
               (args : F.fs tags_t (dir * (E.t tags_t * E.e tags_t)))
               (f x : name tags_t) (i : tags_t) :
        out_update args Γ = Γ' ->
        fns f = Some (E.Arrow params (Some τ)) ->
        F.relfs
          (fun dte dt =>
             fst dt = fst dte /\ E.equivt (snd dt) (dte ▷ snd ▷ fst) /\
             let e := dte ▷ snd ▷ snd in
             let τ := snd dt in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ) args params ->
        (⦃ fns , errs , mkds , Γ ⦄
           ⊢ let x :: τ := call f with args @ i fin ⊣ x ↦ τ ;; Γ', C)
    where "⦃ fe ',' ers ',' mks ',' g1 ⦄ ⊢ s ⊣ g2 ',' sg"
            := (check_stmt fe ers mks g1 s g2 sg).
    (**[]*)

    (** Control Constructors. *)
    Inductive cctor : Type := CCtor (params : F.fs tags_t (E.t tags_t)).

    (** Environment with Controls. *)
    Definition cenv : Type := Env.t (name tags_t) cctor.

    (** Instance environment. *)
    Definition ienv : Type := Env.t (name tags_t) unit.

    (** Put parameters into environment. *)
    Definition bind_all (sig : E.arrowT tags_t) : gam -> gam :=
      match sig with
      | E.Arrow params _ =>
        F.fold (fun x '(_,τ) Γ =>
                  let x' := bare x in
                  !{ x' ↦ τ ;; Γ }!) params
      end.
    (**[]*)

    (** Appropriate signal. *)
    Inductive good_signal : E.arrowT tags_t -> signal -> Prop :=
      | good_signal_cont params :
          good_signal (E.Arrow params None) SIG_Cont
      | good_signal_return params ret :
          good_signal (E.Arrow params (Some ret)) SIG_Return.
    (**[]*)

    Inductive check_decl
              (cs : cenv) (ins : ienv)
              (fns : fenv) (errs : errors)
              (mkds : matchkinds)
              (Γ : gam) : D.d tags_t -> gam -> fenv -> ienv -> Prop :=
    | chk_vardeclare (τ : E.t tags_t) (x : string tags_t) (i : tags_t) :
        let x' := bare x in
        check_decl cs ins fns errs mkds Γ
                   (D.DVardecl τ x i) !{ x' ↦ τ ;; Γ }! fns ins
    | chk_varinit (τ : E.t tags_t) (x : string tags_t)
                  (e : E.e tags_t) (i : tags_t) :
        ⟦ errs, mkds, Γ ⟧ ⊢ e ∈ τ ->
        let x' := bare x in
        check_decl cs ins fns errs mkds Γ
                   (D.DVarinit τ x e i) !{ x' ↦ τ ;; Γ }! fns ins
    | chk_instantiate (c : name tags_t) (x : string tags_t)
                      (params : F.fs tags_t (E.t tags_t))
                      (args : F.fs tags_t (E.t tags_t * E.e tags_t))
                      (i : tags_t) :
        cs c = Some (CCtor params) ->
        F.relfs
          (fun '(τ,e) τ' =>
             E.equivt τ τ' /\ ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ)
          args params ->
        let x' := bare x in
        check_decl cs ins fns errs mkds Γ
                   (D.DInstantiate c x args i) Γ fns !{ x' ↦ tt ;; ins }!
(* Functions belong only to the top-level declarations.
    | chk_function (f : name tags_t) (sig : E.arrowT tags_t)
                   (body : S.s tags_t) (i : tags_t)
                   (Γ' Γ'' : gam) (sg : signal) :
        bind_all sig Γ = Γ' ->
        (⦃ fns, errs, mkds, Γ' ⦄ ⊢ body ⊣ Γ'', sg) ->
        good_signal sig sg ->
        check_decl cs ins fns errs mkds Γ
                   (D.DFunction f sig body i) Γ !{ f ↦ sig ;; fns }! ins *)
    | chk_declseq (d1 d2 : D.d tags_t) (i : tags_t) (ins' ins'' : ienv)
                  (fns' fns'' : fenv) (Γ' Γ'' : gam) :
        check_decl cs ins fns errs mkds Γ d1 Γ' fns' ins' ->
        check_decl cs ins' fns' errs mkds Γ' d2 Γ'' fns'' ins'' ->
        check_decl cs ins fns errs mkds Γ (D.DSeq d1 d2 i) Γ'' fns'' ins''.
    (**[]*)
  End TypeCheck.
End Typecheck.
