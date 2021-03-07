Require Export Coq.PArith.BinPosDef.
Export Pos.
Require Export Coq.NArith.BinNat.
Require Export P4cub.AST.
Require Export P4cub.P4Arith.
Require Export Envn.

(** Notation entries. *)
Declare Custom Entry p4signal.
Declare Custom Entry p4context.

Reserved Notation "⟦ ers , gm ⟧ ⊢ e ∈ t"
         (at level 40, e custom p4expr, t custom p4type at level 0).

Reserved Notation "⦃ fe , ienv , errs , g1 ⦄ ctx ⊢ s ⊣ ⦃ g2 , sg ⦄"
         (at level 40, s custom p4stmt, ctx custom p4context,
          g2 custom p4env, sg custom p4signal).

Reserved Notation "⦗ cenv , fenv , ienv1 , errs , g1 ⦘ ⊢ d ⊣ ⦗ g2 , ienv2 ⦘"
         (at level 50, d custom p4decl, g2 custom p4env, ienv2 custom p4env).

Reserved Notation "⟅ sts , ers , gm ⟆ ⊢ e" (at level 40, e custom p4prsrexpr).

Reserved Notation
         "⦅ tbls1 , acts1 , cenv , fenv , ienv1 , errs , g1 ⦆ ⊢ d ⊣ ⦅ g2 , ienv2 , acts2 , tbls2 ⦆"
         (at level 60, d custom p4ctrldecl, g2 custom p4env,
          ienv2 custom p4env, tbls2 custom p4env, acts2 custom p4env).

Reserved Notation
         "$ cenv1 , fenv1 , ienv1 , errs , g1 $ ⊢ d ⊣ $ g2 , ienv2 , fenv2 , cenv2 $"
         (at level 70, d custom p4topdecl, g2 custom p4env,
          ienv2 custom p4env, fenv2 custom p4env, cenv2 custom p4env).

(** * Typechecking *)
Module Typecheck.
  Module P := P4cub.

  Module E := P.Expr.
  Import E.TypeEquivalence.
  Module PT := E.ProperType.

  Module ST := P.Stmt.
  Module D := P.Decl.
  Module PS := P.Parser.ParserState.
  Module CD := P.Control.ControlDecl.
  Module TD := P.TopDecl.
  Module F := P.F.
  Definition dir := P.Dir.d.

  Import P.P4cubNotations.

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

  Notation "x" := x (in custom p4signal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4signal at level 0).
  Notation "'R'" := SIG_Return (in custom p4signal at level 0).

  Import Env.EnvNotations.

  Section TypeCheckDefs.
    Context {tags_t : Type}.

    (** Available strings. *)
    Definition strs : Type := Env.t (string tags_t) unit.

    (** Available names. *)
    Definition names : Type := Env.t (name tags_t) unit.

    (** Available error names. *)
    Definition errors : Type := strs.

    (** Typing context. *)
    Definition gamma : Type := Env.t (name tags_t) (E.t tags_t).

    Definition bare (x : string tags_t) : name tags_t :=
      Typed.BareName x.
    (**[]*)

    (** Evidence for a type being a numeric of a given width. *)
    Inductive numeric_width (w : positive) : E.t tags_t -> Prop :=
    | numeric_width_bit : numeric_width w {{ bit<w> }}
    | numeric_width_int : numeric_width w {{ int<w> }}.

    (** Evidence for a type being numeric. *)
    Inductive numeric : E.t tags_t -> Prop :=
      Numeric (w : positive) (τ : E.t tags_t) :
        numeric_width w τ -> numeric τ.
    (**[]*)

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

    (** Evidence an error is ok. *)
    Inductive error_ok (errs : errors) : option (string tags_t) -> Prop :=
    | NoErrorOk : error_ok errs None
    | ErrorOk (x : string tags_t) :
        errs x = Some tt ->
        error_ok errs (Some x).
    (**[]*)

    (** Typing header operations. *)
    Definition type_hdr_op
               (op : E.hdr_op) (ts : F.fs tags_t (E.t tags_t))
      : E.t tags_t :=
      match op with
      | E.HOIsValid => {{ Bool }}
      | E.HOSetValid
      | E.HOSetInValid => {{ hdr { ts } }}
      end.
    (**[]*)

    (** Available functions. *)
    Definition fenv : Type := Env.t (name tags_t) (E.arrowT tags_t).

    (** Available actions. *)
    Definition aenv : Type := Env.t (name tags_t) (E.params tags_t).

    (** Instance environment. *)
    Definition ienv : Type := Env.t (name tags_t) (E.params tags_t).

    (** Available table names. *)
    Definition tblenv : Type := names.

    (** Statement context. *)
    Inductive ctx : Type :=
    | CAction (available_actions : aenv)
    | CVoid
    | CFunction (return_type : E.t tags_t)
    | CApplyBlock (tables : tblenv) (available_actions : aenv)
    | CParserState.
    (**[]*)

    (** Evidence an action call context is ok. *)
    Inductive action_call_ok (aa : aenv) : ctx -> Prop :=
    | action_action_ok : action_call_ok aa (CAction aa)
    | action_apply_block_ok (tbls : tblenv) :
        action_call_ok aa (CApplyBlock tbls aa).
    (**[]*)

    (** Evidence an exit context ok. *)
    Inductive exit_ctx_ok : ctx -> Prop :=
    | exit_action_ok (aa : aenv) : exit_ctx_ok (CAction aa)
    | exit_applyblk_ok (tbls : tblenv) (aa : aenv) :
        exit_ctx_ok (CApplyBlock tbls aa).
    (**[]*)

    (** Evidence a void return is ok. *)
    Inductive return_void_ok : ctx -> Prop :=
    | return_void_action (aa : aenv) : return_void_ok (CAction aa)
    | return_void_void : return_void_ok CVoid
    | return_void_applyblk (tbls : tblenv) (aa : aenv) :
        return_void_ok (CApplyBlock tbls aa).
    (**[]*)

    (** Control Constructor Types. *)
    Inductive cctor : Type :=
    | CCtor (cparams : F.fs tags_t (E.t tags_t)) (params : E.params tags_t).
    (**[]*)

    (** Environment with Controls. *)
    Definition cenv : Type := Env.t (name tags_t) cctor.

    (** Put parameters into environment. *)
    Definition bind_all : E.params tags_t -> gamma -> gamma :=
      F.fold (fun x '(P.PAIn τ | P.PAOut τ | P.PAInOut τ) Γ =>
                let x' := bare x in
                !{ x' ↦ τ ;; Γ }!).
    (**[]*)

    (** Put (constructor) parameters into environment. *)
    Definition cbind_all : F.fs tags_t (E.t tags_t) -> gamma -> gamma :=
      F.fold (fun x τ Γ => let x' := bare x in !{ x' ↦ τ ;; Γ }!).
    (**[]*)

    (** Appropriate signal. *)
    Inductive good_signal : E.arrowT tags_t -> signal -> Prop :=
      | good_signal_cont params :
          good_signal (P.Arrow params None) SIG_Cont
      | good_signal_return params ret :
          good_signal (P.Arrow params (Some ret)) SIG_Return.
    (**[]*)

    (** Valid parser states. *)
    Definition states : Type := strs.
  End TypeCheckDefs.

  Notation "x" := x (in custom p4context at level 0, x constr at level 0).
  Notation "'Action' aa" := (CAction aa) (in custom p4context at level 0).
  Notation "'Void'" := CVoid (in custom p4context at level 0).
  Notation "'Function' t"
    := (CFunction t)
         (in custom p4context at level 0, t custom p4type).
  Notation "'ApplyBlock' tbls aa"
           := (CApplyBlock tbls aa)
                (in custom p4context at level 0, tbls custom p4env).
  Notation "'Parser'" := CParserState (in custom p4context at level 0).

  (** Expression typing as a relation. *)
  Inductive check_expr
            {tags_t : Type} (errs : errors) (Γ : gamma) : E.e tags_t -> E.t tags_t -> Prop :=
  (* Literals. *)
  | chk_bool (b : bool) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ BOOL b @ i ∈ Bool
  | chk_bit (w : positive) (n : N) (i : tags_t) :
      BitArith.bound w n ->
      ⟦ errs , Γ ⟧ ⊢ w W n @ i ∈ bit<w>
  | chk_int (w : positive) (n : Z) (i : tags_t) :
      IntArith.bound w n ->
      ⟦ errs , Γ ⟧ ⊢ w S n @ i ∈ int<w>
  | chk_var (x : name tags_t) (τ : E.t tags_t) (i : tags_t) :
      Γ x = Some τ ->
      PT.proper_nesting τ ->
      ⟦ errs , Γ ⟧ ⊢ Var x:τ @ i ∈ τ
  (* Unary operations. *)
  | chk_not (e : E.e tags_t) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ e ∈ Bool ->
      ⟦ errs , Γ ⟧ ⊢ UOP ! e:Bool @ i ∈ Bool
  | chk_bitnot (w : positive) (e : E.e tags_t) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ e ∈ bit<w> ->
      ⟦ errs , Γ ⟧ ⊢ UOP ~ e:bit<w> @ i ∈ bit<w>
  | chk_uminus (w : positive) (e : E.e tags_t) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ e ∈ int<w> ->
      ⟦ errs , Γ ⟧ ⊢ UOP - e:int<w> @ i ∈ int<w>
  (* Binary Operations. *)
  | chk_numeric_bop (op : E.bop) (τ τ' : E.t tags_t)
                    (e1 e2 : E.e tags_t) (i : tags_t) :
      ∫ τ ≡ τ' -> numeric τ -> numeric_bop op ->
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ' ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:τ op e2:τ' @ i ∈ τ
  | chk_comp_bop (op : E.bop) (τ τ' : E.t tags_t)
                 (e1 e2 : E.e tags_t) (i : tags_t) :
      ∫ τ ≡ τ' -> numeric τ -> comp_bop op ->
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ' ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:τ op e2:τ' @ i ∈ Bool
  | chk_bool_bop (op : E.bop) (e1 e2 : E.e tags_t) (i : tags_t) :
      bool_bop op ->
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ Bool ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ Bool ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:Bool op e2:Bool @ i ∈ Bool
  | chk_eq (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:τ == e2:τ @ i ∈ Bool
  | chk_neq (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:τ != e2:τ @ i ∈ Bool
  | chk_plusplus_bit (τ : E.t tags_t) (m n w : positive)
                     (e1 e2 : E.e tags_t) (i : tags_t) :
      (m + n)%positive = w ->
      (* numeric_width n τ -> *)
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ bit<m> ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ bit<n> ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:bit<m> ++ e2:bit<n> @ i ∈ bit<w>
  (* Member expressions. *)
  | chk_hdr_mem (e : E.e tags_t) (x : string tags_t)
                (fields : F.fs tags_t (E.t tags_t))
                (τ : E.t tags_t) (i : tags_t) :
      F.get x fields = Some τ ->
      ⟦ errs , Γ ⟧ ⊢ e ∈ hdr { fields } ->
      ⟦ errs , Γ ⟧ ⊢ Mem e:hdr { fields } dot x @ i ∈ τ
  | chk_rec_mem (e : E.e tags_t) (x : string tags_t)
                (fields : F.fs tags_t (E.t tags_t))
                (τ : E.t tags_t) (i : tags_t) :
      F.get x fields = Some τ ->
      ⟦ errs , Γ ⟧ ⊢ e ∈ rec { fields } ->
      ⟦ errs , Γ ⟧ ⊢ Mem e:rec { fields } dot x @ i ∈ τ
  (* Structs. *)
  | chk_rec_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                (tfs : F.fs tags_t (E.t tags_t)) (i : tags_t) :
      F.relfs
        (fun te τ =>
           equivt (fst te) τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      ⟦ errs , Γ ⟧ ⊢ rec { efs } @ i ∈ rec { tfs }
  | chk_hdr_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                (tfs : F.fs tags_t (E.t tags_t))
                (i : tags_t) (b : E.e tags_t) :
      PT.proper_nesting {{ hdr { tfs } }} ->
      F.relfs
        (fun te τ =>
           equivt (fst te) τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      ⟦ errs, Γ ⟧ ⊢ b ∈ Bool ->
      ⟦ errs , Γ ⟧ ⊢ hdr { efs } valid := b @ i ∈ hdr { tfs }
  (* Errors and matchkinds. *)
  | chk_error (err : option (string tags_t)) (i : tags_t) :
      error_ok errs err ->
      ⟦ errs , Γ ⟧ ⊢ Error err @ i ∈ error
  | chk_matchkind (mkd : E.matchkind) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ Matchkind mkd @ i ∈ matchkind
  | chk_hdr_op (op : E.hdr_op) (e : E.e tags_t) (i : tags_t)
                (τ : E.t tags_t) (ts : F.fs tags_t (E.t tags_t)) :
      type_hdr_op op ts = τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts } ->
      ⟦ errs, Γ ⟧ ⊢ HDR_OP op e @ i ∈ τ
  | chk_stack (ts : F.fs tags_t (E.t tags_t))
              (hs : list (E.e tags_t))
              (n : positive) (ni : N) :
      BitArith.bound 32%positive (Npos n) -> N.lt ni (Npos n) ->
      Pos.to_nat n = length hs ->
      PT.proper_nesting {{ stack ts[n] }} ->
      Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
      ⟦ errs, Γ ⟧ ⊢ Stack hs:ts[n] nextIndex:=ni ∈ stack ts[n]
  | chk_access (e : E.e tags_t) (idx : N) (i : tags_t)
               (ts : F.fs tags_t (E.t tags_t)) (n : positive) :
      N.lt idx (Npos n) ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ stack ts[n] ->
      ⟦ errs, Γ ⟧ ⊢ Access e[idx] @ i ∈ hdr { ts }
  where "⟦ ers ',' gm ⟧ ⊢ e ∈ ty"
          := (check_expr ers gm e ty) : type_scope.
  (**[]*)

  (** Custom induction principle for expression typing. *)
  Section CheckExprInduction.
    Variable (tags_t : Type).

    (** An arbitrary predicate. *)
    Variable P : @errors tags_t -> @gamma tags_t -> E.e tags_t -> E.t tags_t -> Prop.

    Hypothesis HBool : forall errs Γ b i,
      P errs Γ <{ BOOL b @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HBit : forall errs Γ w n i,
        BitArith.bound w n -> P errs Γ <{ w W n @ i }> {{ bit<w> }}.
    (**[]*)

    Hypothesis HInt : forall errs Γ w z i,
        IntArith.bound w z -> P errs Γ <{ w S z @ i }> {{ int<w> }}.
    (**[]*)

    Hypothesis HVar : forall errs Γ x τ i,
        Γ x = Some τ ->
        PT.proper_nesting τ ->
        P errs Γ <{ Var x:τ @ i }> τ.
    (**[]*)

    Hypothesis HNot : forall errs Γ e i,
        ⟦ errs , Γ ⟧ ⊢ e ∈ Bool ->
        P errs Γ e {{ Bool }} ->
        P errs Γ <{ UOP ! e:Bool @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HBitNot : forall errs Γ w e i,
        ⟦ errs , Γ ⟧ ⊢ e ∈ bit<w> ->
        P errs Γ e {{ bit<w> }} ->
        P errs Γ <{ UOP ~ e:bit<w> @ i }> {{ bit<w> }}.
    (**[]*)

    Hypothesis HUMinus : forall errs Γ w e i,
        ⟦ errs , Γ ⟧ ⊢ e ∈ int<w> ->
        P errs Γ e {{ int<w> }} ->
        P errs Γ <{ UOP - e:int<w> @ i }> {{ int<w> }}.
    (**[]*)

    Hypothesis HNumericBOP : forall errs Γ op τ τ' e1 e2 i,
        equivt τ τ' -> numeric τ -> numeric_bop op ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
        P errs Γ e1 τ ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ' ->
        P errs Γ e2 τ' ->
        P errs Γ <{ BOP e1:τ op e2:τ' @ i }> τ.
    (**[]*)

    Hypothesis HCompBOP : forall errs Γ op τ τ' e1 e2 i,
        equivt τ τ' -> numeric τ -> comp_bop op ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
        P errs Γ e1 τ ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ' ->
        P errs Γ e2 τ' ->
        P errs Γ <{ BOP e1:τ op e2:τ' @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HBoolBOP : forall errs Γ op e1 e2 i,
        bool_bop op ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ Bool ->
        P errs Γ e1 {{ Bool }} ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ Bool ->
        P errs Γ e2 {{ Bool }} ->
        P errs Γ <{ BOP e1:Bool op e2:Bool @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HEq : forall errs Γ τ e1 e2 i,
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
        P errs Γ e1 τ ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ ->
        P errs Γ e2 τ ->
        P errs Γ <{ BOP e1:τ == e2:τ @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HNeq : forall errs Γ τ e1 e2 i,
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
        P errs Γ e1 τ ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ ->
        P errs Γ e2 τ ->
        P errs Γ <{ BOP e1:τ != e2:τ @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HPlusPlus : forall errs Γ τ m n w e1 e2 i,
        (m + n)%positive = w ->
        (* numeric_width n τ -> *)
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ bit<m> ->
        P errs Γ e1 {{ bit<m> }} ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ bit<n> ->
        P errs Γ e2 τ ->
        P errs Γ <{ BOP e1:bit<m> ++ e2:bit<n> @ i }> {{ bit<w> }}.
    (**[]*)

    Hypothesis HHdrMem : forall errs Γ e x fields τ i,
        F.get x fields = Some τ ->
        ⟦ errs , Γ ⟧ ⊢ e ∈ hdr { fields } ->
        P errs Γ e {{ hdr { fields } }} ->
        P errs Γ <{ Mem e:hdr { fields } dot x @ i }> τ.
    (**[]*)

    Hypothesis HRecMem : forall errs Γ e x fields τ i,
        F.get x fields = Some τ ->
        ⟦ errs , Γ ⟧ ⊢ e ∈ rec { fields } ->
        P errs Γ e {{ rec { fields } }} ->
        P errs Γ <{ Mem e:rec { fields } dot x @ i }> τ.
    (**[]*)

    Hypothesis HRecLit : forall errs Γ efs tfs i,
        F.relfs
          (fun te τ =>
             equivt (fst te) τ /\
             let e := snd te in
             ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
        F.relfs
          (fun te τ => let e := snd te in P errs Γ e τ)
          efs tfs ->
        P errs Γ <{ rec { efs } @ i }> {{ rec { tfs } }}.
    (**[]*)

    Hypothesis HHdrLit : forall errs Γ efs tfs i b,
        PT.proper_nesting {{ hdr { tfs } }} ->
        F.relfs
          (fun te τ =>
             equivt (fst te) τ /\
             let e := snd te in
             ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
        F.relfs
          (fun te τ => let e := snd te in P errs Γ e τ)
          efs tfs ->
        ⟦ errs, Γ ⟧ ⊢ b ∈ Bool ->
        P errs Γ b {{ Bool }} ->
        P errs Γ <{ hdr { efs } valid:=b @ i }> {{ hdr { tfs } }}.
    (**[]*)

    Hypothesis HError : forall errs Γ err i,
        error_ok errs err ->
        P errs Γ <{ Error err @ i }> {{ error }}.
    (**[]*)

    Hypothesis HMatchKind : forall errs Γ mkd i,
        P errs Γ <{ Matchkind mkd @ i }> {{ matchkind }}.
    (**[]*)

    Hypothesis HValid : forall errs Γ op e i τ ts,
        type_hdr_op op ts = τ ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts } ->
        P errs Γ e {{ hdr { ts } }} ->
        P errs Γ <{ HDR_OP op e @ i }> τ.
    (**[]*)

    Hypothesis HStack : forall errs Γ ts hs n ni,
        BitArith.bound 32%positive (Npos n) -> N.lt ni (Npos n) ->
        Pos.to_nat n = length hs ->
        PT.proper_nesting {{ stack ts[n] }} ->
        Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
        Forall (fun e => P errs Γ e {{ hdr { ts } }}) hs ->
        P errs Γ <{ Stack hs:ts[n] nextIndex:=ni }> {{ stack ts[n] }}.
    (**[]*)

    Hypothesis HAccess : forall errs Γ e idx i ts n,
        N.lt idx (Npos n) ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ stack ts[n] ->
        P errs Γ e {{ stack ts[n] }} ->
        P errs Γ <{ Access e[idx] @ i }> {{ hdr { ts } }}.
    (**[]*)

    (** Custom induction principle for expression typing.
        Do [induction ?H using custom_check_expr_ind]. *)
    Definition custom_check_expr_ind :
      forall (errs : errors) (Γ : gamma) (e : E.e tags_t) (τ : E.t tags_t)
        (HY : ⟦ errs, Γ ⟧ ⊢ e ∈ τ), P errs Γ e τ :=
          fix chind errs Γ e τ HY :=
            let fix lind
                    {es : list (E.e tags_t)} {τ : E.t tags_t}
                    (HRs : Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es)
                : Forall (fun e => P errs Γ e τ) es :=
                match HRs with
                | Forall_nil _ => Forall_nil _
                | Forall_cons _
                              Hhead Htail => Forall_cons _
                                                        (chind _ _ _ _ Hhead)
                                                        (lind Htail)
                end in
            let fix fields_ind
                    {efs : F.fs tags_t (E.t tags_t * E.e tags_t)}
                    {tfs : F.fs tags_t (E.t tags_t)}
                    (HRs : F.relfs
                             (fun te τ =>
                                equivt (fst te) τ /\
                                let e := snd te in
                                ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs)
                : F.relfs
                    (fun te τ => let e := snd te in P errs Γ e τ)
                    efs tfs :=
                match HRs
                      in (Forall2 _ es ts)
                      return
                      (Forall2
                         (F.relf (fun te τ => let e := snd te in P errs Γ e τ))
                         es ts) with
                | Forall2_nil _ => Forall2_nil
                                    (F.relf
                                       (fun te τ => let e := snd te in P errs Γ e τ))
                | Forall2_cons te τ
                               (conj HName (conj _ Hhead))
                               Htail => Forall2_cons
                                         te τ
                                         (conj HName (chind errs Γ _ _ Hhead))
                                         (fields_ind Htail)
                end in
            match HY in ⟦ _, _ ⟧ ⊢ e' ∈ τ' return P errs Γ e' τ' with
            | chk_bool _ _ b i     => HBool errs Γ b i
            | chk_bit _ _ _ _ i HB => HBit _ _ _ _ i HB
            | chk_int _ _ _ _ i HB => HInt _ _ _ _ i HB
            | chk_var _ _ _ _ i HP HV => HVar _ _ _ _ i HP HV
            | chk_not _ _ _ i He   => HNot
                                       _ _ _ i He
                                       (chind _ _ _ _ He)
            | chk_bitnot _ _ _ _ i He => HBitNot
                                          _ _ _ _ i He
                                          (chind _ _ _ _ He)
            | chk_uminus _ _ _ _ i He => HUMinus
                                          _ _ _ _ i He
                                          (chind _ _ _ _ He)
            | chk_numeric_bop _ _ _ _ _ _ _ i
                              Hequiv Hnum Hnumbop
                              He1 He2 => HNumericBOP
                                          _ _ _ _ _ _ _ i
                                          Hequiv Hnum Hnumbop
                                          He1 (chind _ _ _ _ He1)
                                          He2 (chind _ _ _ _ He2)
            | chk_comp_bop _ _ _ _ _ _ _ i
                           Hequiv Hnum Hcomp
                           He1 He2 => HCompBOP
                                       _ _ _ _ _ _ _ i
                                       Hequiv Hnum Hcomp
                                       He1 (chind _ _ _ _ He1)
                                       He2 (chind _ _ _ _ He2)
            | chk_bool_bop _ _ _ _ _ i Hboolbop
                           He1 He2 => HBoolBOP
                                       _ _ _ _ _ i Hboolbop
                                       He1 (chind _ _ _ _ He1)
                                       He2 (chind _ _ _ _ He2)
            | chk_eq _ _ _ _ _ i
                     He1 He2 => HEq
                                 _ _ _ _ _ i
                                 He1 (chind _ _ _ _ He1)
                                 He2 (chind _ _ _ _ He2)
            | chk_neq _ _ _ _ _ i
                      He1 He2 => HNeq
                                  _ _ _ _ _ i
                                  He1 (chind _ _ _ _ He1)
                                  He2 (chind _ _ _ _ He2)
            | chk_plusplus_bit _ _ _ _ _ _ _ _ i
                               Hmnw
                               He1 He2 => HPlusPlus
                                           _ _ _ _ _ _ _ _ i Hmnw
                                           He1 (chind _ _ _ _ He1)
                                           He2 (chind _ _ _ _ He2)
            | chk_hdr_mem _ _ _ x _ _ i
                          HIn He => HHdrMem
                                     _ _ _ x _ _ i HIn
                                     He (chind _ _ _ _ He)
            | chk_rec_mem _ _ _ x _ _ i
                          HIn He => HRecMem
                                     _ _ _ x _ _ i HIn
                                     He (chind _ _ _ _ He)
            | chk_error _ _ _ i HOK => HError errs Γ _ i HOK
            | chk_matchkind _ _ mk i  => HMatchKind errs Γ mk i
            | chk_hdr_op _ _ _ _ i _ _
                         Hhop He => HValid
                                     _ _ _ _ i _ _ Hhop
                                     He (chind _ _ _ _ He)
            | chk_rec_lit _ _ _ _ i
                          HRs => HRecLit
                                  _ _ _ _ i
                                  HRs (fields_ind HRs)
            | chk_hdr_lit _ _ _ _ i _
                          HP HRs Hb => HHdrLit
                                        _ _ _ _ i _ HP
                                        HRs (fields_ind HRs)
                                        Hb (chind _ _ _ _ Hb)
            | chk_stack _ _ _ _ _ ni
                        Hn Hnin Hlen
                        HP HRs => HStack _ _ _ _ _ ni Hn Hnin Hlen HP HRs (lind HRs)
            | chk_access _ _ _ _ i _ _
                         Hidx He => HAccess _ _ _ _ i _ _ Hidx
                                           He (chind _ _ _ _ He)
            end.
     (**[]*)
  End CheckExprInduction.

  (** Statement typing. *)
  Inductive check_stmt
            {tags_t : Type} (fns : fenv) (ins : ienv)
            (errs : errors) (Γ : gamma) : ctx -> ST.s tags_t -> gamma -> signal -> Prop :=
  | chk_skip (i : tags_t) (con : ctx) :
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ skip @ i ⊣ ⦃ Γ, C ⦄
  | chk_seq_cont (s1 s2 : ST.s tags_t) (Γ' Γ'' : gamma)
                 (i : tags_t) (sig : signal) (con : ctx) :
      ⦃ fns, ins, errs, Γ  ⦄ con ⊢ s1 ⊣ ⦃ Γ', C ⦄ ->
      ⦃ fns, ins, errs, Γ' ⦄ con ⊢ s2 ⊣ ⦃ Γ'', sig ⦄ ->
      ⦃ fns, ins, errs, Γ  ⦄ con ⊢ s1 ; s2 @ i ⊣ ⦃ Γ'', sig ⦄
  | chk_vardecl (τ : E.t tags_t) (x : string tags_t) (i : tags_t) (con : ctx) :
      let x' := bare x in
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ var x:τ @ i ⊣ ⦃ x' ↦ τ ;; Γ, C ⦄
  | chk_assign (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) (con : ctx) :
      ⟦ errs, Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs, Γ ⟧ ⊢ e2 ∈ τ ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ asgn e1 := e2 : τ @ i ⊣ ⦃ Γ, C ⦄
  | chk_cond (guard : E.e tags_t) (tru fls : ST.s tags_t)
             (Γ1 Γ2 : gamma) (i : tags_t) (sgt sgf sg : signal) (con : ctx) :
      lub sgt sgf = sg ->
      ⟦ errs, Γ ⟧ ⊢ guard ∈ Bool ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ tru ⊣ ⦃ Γ1, sgt ⦄ ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ fls ⊣ ⦃ Γ2, sgf ⦄ ->
      ⦃ fns, ins, errs, Γ ⦄
        con ⊢ if guard:Bool then tru else fls @ i ⊣ ⦃ Γ, sg ⦄
  | chk_return_void (i : tags_t) (con : ctx) :
      return_void_ok con ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ returns @ i ⊣ ⦃ Γ, R ⦄
  | chk_return_fruit (τ' τ : E.t tags_t) (e : E.e tags_t) (i : tags_t) :
      ∫ τ ≡ τ' ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⦃ fns, ins, errs, Γ ⦄ Function τ' ⊢ return e:τ @ i ⊣ ⦃ Γ, R ⦄
  | chk_exit (i : tags_t) (con : ctx) :
      exit_ctx_ok con ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ exit @ i ⊣ ⦃ Γ, R ⦄
  | chk_void_call (params : E.params tags_t)
                  (args : E.args tags_t)
                  (f : name tags_t) (i : tags_t) (con : ctx) :
      fns f = Some (P.Arrow params None) ->
      F.relfs
        (P.rel_paramarg_same
           (fun '(t,e) τ => ∫ τ ≡ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
        args params ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ call f with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_act_call (params : E.params tags_t)
                 (args : E.args tags_t)
                 (a : name tags_t) (i : tags_t)
                 (aa : aenv) (con : ctx) :
      action_call_ok aa con ->
      aa a = Some params ->
      F.relfs
        (P.rel_paramarg_same
           (fun '(t,e) τ => ∫ τ ≡ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
        args params ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ calling a with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_fun_call (τ : E.t tags_t) (e : E.e tags_t)
                 (params : E.params tags_t)
                 (args : E.args tags_t)
                 (f : name tags_t) (i : tags_t) (con : ctx) :
      fns f = Some (P.Arrow params (Some τ)) ->
      F.relfs
        (P.rel_paramarg_same
           (fun '(t,e) τ => ∫ τ ≡ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
        args params ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⦃ fns, ins, errs , Γ ⦄
        con ⊢ let e : τ := call f with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_apply (args : E.args tags_t) (x : name tags_t)
              (i : tags_t) (params : E.params tags_t) (con : ctx) :
      ins x = Some params ->
      F.relfs
        (P.rel_paramarg_same
           (fun '(t,e) τ => ∫ τ ≡ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
        args params ->
      ⦃ fns, ins, errs, Γ ⦄ con ⊢ apply x with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_invoke (tbl : name tags_t) (i : tags_t)
               (tbls : tblenv) (aa : aenv) :
      tbls tbl = Some tt ->
      ⦃ fns, ins, errs, Γ ⦄ ApplyBlock tbls aa ⊢ invoke tbl @ i ⊣ ⦃ Γ, C ⦄
  where "⦃ fe , ins , ers , g1 ⦄ con ⊢ s ⊣ ⦃ g2 , sg ⦄"
          := (check_stmt fe ins ers g1 con s g2 sg).
  (**[]*)

  (** Declaration typing. *)
  Inductive check_decl
          {tags_t : Type} (cs : cenv) (fns : @fenv tags_t)
          (ins : ienv) (errs : errors)
          (Γ : gamma) : D.d tags_t -> gamma -> ienv -> Prop :=
  | chk_vardeclare (τ : E.t tags_t) (x : string tags_t) (i : tags_t) :
      PT.proper_nesting τ ->
      let x' := bare x in
      ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ Var x:τ @ i ⊣ ⦗ x' ↦ τ ;; Γ, ins ⦘
  | chk_varinit (τ : E.t tags_t) (x : string tags_t)
                (e : E.e tags_t) (i : tags_t) :
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      let x' := bare x in
      ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ Let x:τ := e @ i ⊣ ⦗ x' ↦ τ ;; Γ, ins ⦘
  | chk_instantiate (c : name tags_t) (x : string tags_t)
                    (cparams : F.fs tags_t (E.t tags_t))
                    (cargs : F.fs tags_t (E.t tags_t * E.e tags_t))
                    (i : tags_t) (params : E.params tags_t) :
      cs c = Some (CCtor cparams params) ->
      F.relfs
        (fun '(τ,e) τ' =>
           ∫ τ ≡ τ' /\ ⟦ errs , Γ ⟧ ⊢ e ∈ τ)
        cargs cparams ->
      let x' := bare x in
      ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ Instance x of c(cargs) @ i ⊣ ⦗ Γ, x' ↦ params ;; ins ⦘
  | chk_declseq (d1 d2 : D.d tags_t) (i : tags_t)
                (ins' ins'' : ienv) (Γ' Γ'' : gamma) :
      ⦗ cs, fns, ins,  errs, Γ  ⦘ ⊢ d1 ⊣ ⦗ Γ',  ins' ⦘ ->
      ⦗ cs, fns, ins', errs, Γ' ⦘ ⊢ d2 ⊣ ⦗ Γ'', ins'' ⦘ ->
      ⦗ cs, fns, ins,  errs, Γ  ⦘ ⊢ d1 ;; d2 @ i ⊣ ⦗ Γ'', ins'' ⦘
  where "⦗ cenv , fenv , ienv1 , errs , g1 ⦘ ⊢ d ⊣ ⦗ g2 , ienv2 ⦘"
          := (check_decl cenv fenv ienv1 errs g1 d g2 ienv2).
  (**[]*)

  (** Parser-expression typing. *)
  Inductive check_prsrexpr {tags_t : Type} (sts : states) (errs : errors) (Γ : gamma)
    : PS.e tags_t -> Prop :=
  | chk_accept (i : tags_t) : ⟅ sts, errs, Γ ⟆ ⊢ accept @ i
  | chk_reject (i : tags_t) : ⟅ sts, errs, Γ ⟆ ⊢ reject @ i
  | chk_goto_state (st : string tags_t) (i : tags_t) :
      sts st = Some tt ->
      ⟅ sts, errs, Γ ⟆ ⊢ goto st @ i
  | chk_select (e : E.e tags_t)
               (cases : list (option (E.e tags_t) * PS.e tags_t))
               (i : tags_t) (τ : E.t tags_t) :
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      Forall
        (fun oe =>
           let o := fst oe in
           let e := snd oe in
           ⟅ sts, errs, Γ ⟆ ⊢ e /\
                        match o with
                        | None => True
                        | Some e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ
                        end) cases ->
      ⟅ sts, errs, Γ ⟆ ⊢ select e { cases } @ i
  where "⟅ sts , ers , gm ⟆ ⊢ e"
          := (check_prsrexpr sts ers gm e).
  (**[]*)

  (** A custom induction principle for parser-expression typing. *)
  Section CheckParserExprInduction.
    Context {tags_t: Type}.

    (** An arbitrary predicate. *)
    Variable P : @states tags_t -> @errors tags_t -> @gamma tags_t -> PS.e tags_t -> Prop.

    Hypothesis HAccept : forall sts errs Γ i, P sts errs Γ p{ accept @ i }p.

    Hypothesis HReject : forall sts errs Γ i, P sts errs Γ p{ reject @ i }p.

    Hypothesis HGotoState : forall sts errs Γ st i,
        sts st = Some tt ->
        P sts errs Γ p{ goto st @ i }p.

    Hypothesis HSelect : forall sts errs Γ e cases i τ,
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        Forall
          (fun oe =>
             let o := fst oe in let e := snd oe in
             ⟅ sts, errs, Γ ⟆ ⊢ e /\
                          match o with
                          | None => True
                          | Some e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ
                          end) cases ->
        Forall
          (fun oe =>
             let e := snd oe in
             P sts errs Γ e) cases ->
        P sts errs Γ p{ select e { cases } @ i }p.

    (** Custom induction principle.
        Do [induction ?H using custom_check_prsrexpr_ind] *)
    Definition custom_check_prsrexpr_ind :
      forall (sts : states) (errs : errors) (Γ : gamma) (e : PS.e tags_t)
        (Hy : ⟅ sts, errs, Γ ⟆ ⊢ e), P sts errs Γ e :=
      fix chind sts errs Γ e Hy :=
        let fix lind
                {cases : list (option (E.e tags_t) * PS.e tags_t)} {τ : E.t tags_t}
                (HR : Forall
                        (fun oe =>
                           let o := fst oe in
                           let e := snd oe in
                           ⟅ sts, errs, Γ ⟆ ⊢ e /\
                                        match o with
                                        | None => True
                                        | Some e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ
                                        end) cases)
            : Forall (fun oe => P sts errs Γ (snd oe)) cases :=
            match HR with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ (conj He _) Htail => Forall_cons
                                                  _
                                                  (chind _ _ _ _ He)
                                                  (lind Htail)
            end in
        match Hy with
        | chk_accept _ _ _ i => HAccept _ _ _ i
        | chk_reject _ _ _ i => HReject _ _ _ i
        | chk_goto_state _ _ _ _ Hst i => HGotoState _ _ _ _ Hst i
        | chk_select _ _ _ _ _ i _
                     He Hcases => HSelect _ _ _ _ _ i _ He
                                         Hcases (lind Hcases)
        end.
    (**[]*)
  End CheckParserExprInduction.

  (** Parser State typing. *)
  Inductive check_state
            {tags_t : Type} (fns : fenv) (ins : ienv) (sts : states)
            (errs : errors) (Γ : gamma) : PS.state tags_t -> Prop :=
  | chk_state (s : ST.s tags_t) (e : PS.e tags_t)
              (Γ' : gamma) (sg : signal) :
      ⦃ fns , ins , errs , Γ ⦄ Parser ⊢ s ⊣ ⦃ Γ' , sg ⦄ ->
      ⟅ sts, errs, Γ' ⟆ ⊢ e ->
      check_state fns ins sts errs Γ &{ state { s } transition e }&.
  (**[]*)

  (** Control declaration typing. *)
  Inductive check_ctrldecl
            {tags_t : Type} (tbls : tblenv) (acts : aenv) (cs : cenv) (fns : fenv)
            (ins : ienv) (errs : errors) (Γ : gamma)
    : CD.d tags_t -> gamma -> ienv -> aenv -> tblenv -> Prop :=
  | chk_action (a : string tags_t)
               (signature : E.params tags_t)
               (body : ST.s tags_t) (i : tags_t)
               (Γ' Γ'' : gamma) (sg : signal) :
      let a' := bare a in
      bind_all signature Γ = Γ' ->
      ⦃ fns, ins, errs, Γ ⦄ Action acts ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      ⦅ tbls, acts, cs, fns, ins, errs, Γ ⦆
        ⊢ action a ( signature ) { body } @ i
        ⊣ ⦅ Γ, ins, a' ↦ signature ;; acts, tbls ⦆
  | chk_table (t : string tags_t)
              (kys : list
                        (E.t tags_t * E.e tags_t * E.matchkind))
              (actns : list (string tags_t))
              (i : tags_t) :
      (* Keys type. *)
      Forall (fun '(τ,e,_) => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) kys ->
      (* Actions available *)
      Forall
        (fun a => exists pms, let a' := bare a in acts a' = Some pms)
        actns ->
      let t' := bare t in
      ⦅ tbls, acts, cs, fns, ins, errs, Γ ⦆
        ⊢ table t key:=kys actions:=actns @ i ⊣ ⦅ Γ, ins, acts, t' ↦ tt;; tbls ⦆
  | chk_decl (d : D.d tags_t) (i : tags_t)
             (Γ' : gamma) (ins' : ienv) :
      ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ d ⊣ ⦗ Γ', ins' ⦘ ->
      ⦅ tbls, acts, cs, fns, ins, errs, Γ ⦆ ⊢ Decl d @ i ⊣ ⦅ Γ', ins', acts, tbls ⦆
  | chk_ctrldecl_seq (d1 d2 : CD.d tags_t) (i : tags_t)
                     (Γ' Γ'' : gamma) (ins' ins'' : ienv)
                     (acts' acts'' : aenv) (tbls' tbls'' : tblenv) :
      ⦅ tbls,  acts,  cs, fns, ins,  errs, Γ  ⦆ ⊢ d1 ⊣ ⦅ Γ',  ins',  acts',  tbls'  ⦆ ->
      ⦅ tbls', acts', cs, fns, ins', errs, Γ' ⦆ ⊢ d2 ⊣ ⦅ Γ'', ins'', acts'', tbls'' ⦆ ->
      ⦅ tbls,  acts,  cs, fns, ins,  errs, Γ  ⦆
        ⊢ d1 ;c; d2 @ i ⊣ ⦅ Γ'', ins'', acts'', tbls'' ⦆
  where
  "⦅ tbls1 , acts1 , cenv , fenv , ienv1 , errs , g1 ⦆ ⊢ d ⊣ ⦅ g2 , ienv2 , acts2 , tbls2 ⦆"
    := (check_ctrldecl tbls1 acts1 cenv fenv ienv1 errs g1 d g2 ienv2 acts2 tbls2).
  (**[]*)

  (** Top-level declaration typing. *)
  Inductive check_topdecl
            {tags_t : Type} (cs : cenv) (fns : fenv)
            (ins : ienv) (errs : errors) (Γ : gamma)
            : TD.d tags_t -> gamma -> ienv -> fenv -> cenv -> Prop :=
  | chk_control (c : string tags_t) (cparams : F.fs tags_t (E.t tags_t))
                (params : E.params tags_t) (body : CD.d tags_t)
                (apply_blk : ST.s tags_t) (i : tags_t)
                (Γ' Γ'' Γ''' Γ'''' : gamma) (sg : signal)
                (tbls : tblenv) (acts : aenv) (ins' ins'' : @ienv tags_t) :
      cbind_all cparams Γ = Γ' ->
      let empty_tbls := Env.empty (name tags_t) unit in
      let empty_acts := Env.empty (name tags_t) (E.params tags_t) in
      (* Control declarations. *)
      ⦅ empty_tbls, empty_acts, cs, fns, ins, errs, Γ' ⦆
        ⊢ body ⊣ ⦅ Γ'', ins', acts, tbls ⦆ ->
      bind_all params Γ'' = Γ''' ->
      (* Apply block. *)
      ⦃ fns, ins', errs, Γ''' ⦄ ApplyBlock tbls acts ⊢ apply_blk ⊣ ⦃ Γ'''', sg ⦄ ->
      let c' := bare c in
      let ctor := CCtor cparams params in
      $ cs, fns, ins, errs, Γ $
        ⊢ control c (cparams)(params) apply { apply_blk } where { body } @ i
        ⊣ $ Γ, ins, fns, c' ↦ ctor;; cs $
  | chk_parser (p : string tags_t) (cparams : F.fs tags_t (E.t tags_t))
               (params : E.params tags_t)
               (states : F.fs tags_t (PS.state tags_t)) (i : tags_t)
               (Γ' Γ'' : gamma) :
      let empty_sts := Env.empty (string tags_t) unit in
      let sts := fold_right
                   (fun '(st,_) acc => !{ st ↦ tt;; acc }!)
                   empty_sts states in
      cbind_all cparams Γ = Γ' ->
      bind_all params Γ' = Γ'' ->
      Forall
        (fun '(_,pst) => check_state fns ins sts errs Γ'' pst)
        states ->
      $ cs, fns, ins, errs, Γ $
        ⊢ parser p (cparams)(params) { states } @ i ⊣ $ Γ, ins, fns, cs $
  | chk_fruit_function (f : string tags_t) (params : E.params tags_t)
                       (τ : E.t tags_t) (body : ST.s tags_t) (i : tags_t)
                       (Γ' Γ'' : gamma) (sg : signal) :
      bind_all params Γ = Γ' ->
      ⦃ fns, ins, errs, Γ' ⦄ Function τ ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      let f' := bare f in
      let func := P.Arrow params (Some τ) in
      $ cs, fns, ins, errs, Γ $
        ⊢ fn f (params) -> τ { body } @ i ⊣ $ Γ, ins, f' ↦ func;;  fns, cs $
  | chk_void_function (f : string tags_t) (params : E.params tags_t)
                      (body : ST.s tags_t) (i : tags_t)
                      (Γ' Γ'' : gamma) (sg : signal) :
      bind_all params Γ = Γ' ->
      ⦃ fns, ins, errs, Γ' ⦄ Void ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      let f' := bare f in
      let func := P.Arrow params None in
      $ cs, fns, ins, errs, Γ $
        ⊢ void f (params) { body } @ i ⊣ $ Γ, ins, f' ↦ func;;  fns, cs $
  | chk_topdecl (d : D.d tags_t) (i : tags_t)
                (Γ' : gamma) (ins' : ienv) :
      ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ d ⊣ ⦗ Γ', ins' ⦘ ->
      $ cs, fns, ins, errs, Γ $ ⊢ DECL d @ i ⊣ $ Γ', ins', fns, cs $
  | chk_topdecl_seq (d1 d2 : TD.d tags_t) (i : tags_t)
                    (Γ' Γ'' : gamma) (ins' ins'' : ienv)
                    (fns' fns'' : fenv) (cs' cs'' : cenv) :
      $ cs,  fns,  ins,  errs, Γ  $ ⊢ d1 ⊣ $ Γ',  ins',  fns',  cs'  $ ->
      $ cs', fns', ins', errs, Γ' $ ⊢ d2 ⊣ $ Γ'', ins'', fns'', cs'' $ ->
      $ cs,  fns,  ins,  errs, Γ  $ ⊢ d1 ;%; d2 @ i ⊣ $ Γ'', ins'', fns'', cs'' $
  where
  "$ cenv1 , fenv1 , ienv1 , errs , g1 $ ⊢ d ⊣ $ g2 , ienv2 , fenv2 , cenv2 $"
    := (check_topdecl cenv1 fenv1 ienv1 errs g1 d g2 ienv2 fenv2 cenv2).
  (**[]*)
End Typecheck.
