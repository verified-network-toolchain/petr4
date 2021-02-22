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

  Import D.DeclNotations.

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

  Notation "x" := x (in custom p4signal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4signal at level 0).
  Notation "'R'" := SIG_Return (in custom p4signal at level 0).

  Reserved Notation "⟦ ers , gm ⟧ ⊢ e ∈ t"
           (at level 40, e custom p4expr, t custom p4type at level 0).

  Import Env.EnvNotations.

  Declare Custom Entry p4context.

  Reserved Notation "⦃ fe , ienv , errs , g1 ⦄ ctx ⊢ s ⊣ ⦃ g2 , sg ⦄"
           (at level 40, s custom p4stmt, ctx custom p4context,
            g2 custom p4env, sg custom p4signal).

  Reserved Notation "⦗ cenv , fenv , ienv1 , errs , g1 ⦘ ⊢ d ⊣ ⦗ g2 , ienv2 ⦘"
           (at level 50, d custom p4decl, g2 custom p4env, ienv2 custom p4env).

  Section TypeCheck.
    Variable (tags_t : Type).

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
               (op : E.hdr_op) (ts : F.fs tags_t (E.t tags_t)) : E.t tags_t :=
      match op with
      | E.HOIsValid => {{ Bool }}
      | E.HOSetValid
      | E.HOSetInValid => {{ hdr { ts } }}
      end.
    (**[]*)

    (** Expression typing as a relation. *)
    Inductive check
              (errs : errors) (Γ : gam) : E.e tags_t -> E.t tags_t -> Prop :=
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
        E.equivt τ τ' -> numeric τ -> numeric_bop op ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ' ->
        ⟦ errs , Γ ⟧ ⊢ BOP e1:τ op e2:τ' @ i ∈ τ
    | chk_comp_bop (op : E.bop) (τ τ' : E.t tags_t)
                   (e1 e2 : E.e tags_t) (i : tags_t) :
        E.equivt τ τ' -> numeric τ -> comp_bop op ->
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
        numeric_width n τ ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ bit<m> ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ ->
        ⟦ errs , Γ ⟧ ⊢ BOP e1:bit<m> ++ e2:τ @ i ∈ bit<w>
    (* Member expressions. *)
    | chk_hdr_mem (e : E.e tags_t) (x : string tags_t)
                  (fields : F.fs tags_t (E.t tags_t))
                  (τ : E.t tags_t) (i : tags_t) :
        In (x, τ) fields ->
        ⟦ errs , Γ ⟧ ⊢ e ∈ hdr { fields } ->
        ⟦ errs , Γ ⟧ ⊢ Mem e:hdr { fields } dot x @ i ∈ τ
    | chk_rec_mem (e : E.e tags_t) (x : string tags_t)
                  (fields : F.fs tags_t (E.t tags_t))
                  (τ : E.t tags_t) (i : tags_t) :
        In (x, τ) fields ->
        ⟦ errs , Γ ⟧ ⊢ e ∈ rec { fields } ->
        ⟦ errs , Γ ⟧ ⊢ Mem e:rec { fields } dot x @ i ∈ τ
    (* Structs. *)
    | chk_rec_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (tfs : F.fs tags_t (E.t tags_t)) (i : tags_t) :
        F.relfs
          (fun te τ =>
             E.equivt (fst te) τ /\
             let e := snd te in
             ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
        ⟦ errs , Γ ⟧ ⊢ rec { efs } @ i ∈ rec { tfs }
    | chk_hdr_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (tfs : F.fs tags_t (E.t tags_t))
                  (i : tags_t) (b : E.e tags_t) :
        F.relfs
          (fun te τ =>
             E.equivt (fst te) τ /\
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
    | chk_isvalid (op : E.hdr_op) (e : E.e tags_t) (i : tags_t)
                  (τ : E.t tags_t) (ts : F.fs tags_t (E.t tags_t)) :
        type_hdr_op op ts = τ ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts } ->
        ⟦ errs, Γ ⟧ ⊢ H op e @ i ∈ τ
    where "⟦ ers ',' gm ⟧ ⊢ e ∈ ty"
            := (check ers gm e ty).
    (**[]*)

    (** Available functions. *)
    Definition fenv : Type := Env.t (name tags_t) (E.arrowT tags_t).

    (** Instance environment. *)
    Definition ienv : Type := Env.t (name tags_t) (E.params tags_t).

    (** Available table names. *)
    Definition tblenv : Type := Env.t (name tags_t) unit.

    (** Statement context. *)
    Inductive ctx : Type :=
    | CAction
    | CMethod
    | CFunction (return_type : E.t tags_t)
    | CApplyBlock (tables : tblenv).
    (**[]*)

    (** Evidence an exit context ok. *)
    Inductive exit_ctx_ok : ctx -> Prop :=
    | exit_action_ok : exit_ctx_ok CAction
    | exit_applyblk_ok (tables : tblenv) : exit_ctx_ok (CApplyBlock tables).
    (**[]*)

    (** Evidence a void return is ok. *)
    Inductive return_void_ok : ctx -> Prop :=
    | return_void_action : return_void_ok CAction
    | return_void_method : return_void_ok CMethod
    | return_void_applyblk (tbls : tblenv) : return_void_ok (CApplyBlock tbls).
    (**[]*)

    Notation "x" := x (in custom p4context at level 0, x constr at level 0).
    Notation "'Action'" := CAction (in custom p4context at level 0).
    Notation "'Method'" := CMethod (in custom p4context at level 0).
    Notation "'Function' t"
      := (CFunction t)
           (in custom p4context at level 0, t custom p4type).
    Notation "'ApplyBlock' tbls"
             := (CApplyBlock tbls)
                  (in custom p4context at level 0, tbls custom p4env).

    Inductive check_stmt
              (fns : fenv) (ins : ienv)
              (errs : errors) (Γ : gam) : ctx -> ST.s tags_t -> gam -> signal -> Prop :=
    | chk_skip (i : tags_t) (con : ctx) :
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ skip @ i ⊣ ⦃ Γ, C ⦄
    | chk_seq_cont (s1 s2 : ST.s tags_t) (Γ' Γ'' : gam)
                   (i : tags_t) (sig : signal) (con : ctx) :
        ⦃ fns, ins, errs, Γ  ⦄ con ⊢ s1 ⊣ ⦃ Γ', C ⦄ ->
        ⦃ fns, ins, errs, Γ' ⦄ con ⊢ s2 ⊣ ⦃ Γ'', sig ⦄ ->
        ⦃ fns, ins, errs, Γ  ⦄ con ⊢ s1 ; s2 @ i ⊣ ⦃ Γ'', sig ⦄
    | chk_seq_ret (s1 s2 : ST.s tags_t) (Γ' : gam) (i : tags_t) (con : ctx) :
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ s1 ⊣ ⦃ Γ', R ⦄ ->
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ s1 ; s2 @ i ⊣ ⦃ Γ', R ⦄
    | chk_vardecl (τ : E.t tags_t) (x : string tags_t) (i : tags_t) (con : ctx) :
        let x' := bare x in
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ var x:τ @ i ⊣ ⦃ x' ↦ τ ;; Γ, C ⦄
    | chk_assign (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t) (con : ctx) :
        ⟦ errs, Γ ⟧ ⊢ e1 ∈ τ ->
        ⟦ errs, Γ ⟧ ⊢ e2 ∈ τ ->
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ asgn e1 := e2 : τ @ i ⊣ ⦃ Γ, C ⦄
    | chk_cond (guard : E.e tags_t) (tru fls : ST.s tags_t)
               (Γ1 Γ2 : gam) (i : tags_t) (sgt sgf sg : signal) (con : ctx) :
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
        E.equivt τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        ⦃ fns, ins, errs, Γ ⦄ Function τ' ⊢ return e:τ @ i ⊣ ⦃ Γ, R ⦄
    | chk_exit (i : tags_t) (con : ctx) :
        exit_ctx_ok con ->
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ exit @ i ⊣ ⦃ Γ, R ⦄
    | chk_method_call (params : E.params tags_t)
                      (args : E.args tags_t)
                      (f : name tags_t) (i : tags_t) (con : ctx) :
        fns f = Some (P.Arrow params None) ->
        F.relfs
          (P.rel_paramarg_same
             (fun '(t,e) τ => E.equivt τ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
          args params ->
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ call f with args @ i ⊣ ⦃ Γ, C ⦄
    | chk_call (τ : E.t tags_t) (e : E.e tags_t)
               (params : E.params tags_t)
               (args : E.args tags_t)
               (f : name tags_t) (i : tags_t) (con : ctx) :
        fns f = Some (P.Arrow params (Some τ)) ->
        F.relfs
          (P.rel_paramarg_same
             (fun '(t,e) τ => E.equivt τ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
          args params ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        ⦃ fns, ins, errs , Γ ⦄
          con ⊢ let e : τ := call f with args @ i ⊣ ⦃ Γ, C ⦄
    | chk_apply (args : E.args tags_t) (x : name tags_t)
                (i : tags_t) (params : E.params tags_t) (con : ctx) :
        ins x = Some params ->
        F.relfs
          (P.rel_paramarg_same
             (fun '(t,e) τ => E.equivt τ t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
          args params ->
        ⦃ fns, ins, errs, Γ ⦄ con ⊢ apply x with args @ i ⊣ ⦃ Γ, C ⦄
    | chk_invoke (tbl : name tags_t) (i : tags_t) (tbls : tblenv) :
        tbls tbl = Some tt ->
        ⦃ fns, ins, errs, Γ ⦄ ApplyBlock tbls ⊢ invoke tbl @ i ⊣ ⦃ Γ, C ⦄
    where "⦃ fe , ins , ers , g1 ⦄ con ⊢ s ⊣ ⦃ g2 , sg ⦄"
            := (check_stmt fe ins ers g1 con s g2 sg).
    (**[]*)

    (** Control Constructor Types. *)
    Inductive cctor : Type :=
    | CCtor (cparams : F.fs tags_t (E.t tags_t)) (params : E.params tags_t).
    (**[]*)

    (** Environment with Controls. *)
    Definition cenv : Type := Env.t (name tags_t) cctor.

    (** Put parameters into environment. *)
    Definition bind_all (sig : E.arrowT tags_t) : gam -> gam :=
      match sig with
      | P.Arrow params _ =>
        F.fold (fun x '(P.PAIn τ | P.PAOut τ | P.PAInOut τ) Γ =>
                  let x' := bare x in
                  !{ x' ↦ τ ;; Γ }!) params
      end.
    (**[]*)

    (** Appropriate signal. *)
    Inductive good_signal : E.arrowT tags_t -> signal -> Prop :=
      | good_signal_cont params :
          good_signal (P.Arrow params None) SIG_Cont
      | good_signal_return params ret :
          good_signal (P.Arrow params (Some ret)) SIG_Return.
    (**[]*)

    Inductive check_decl
              (cs : cenv) (fns : fenv)
              (ins : ienv) (errs : errors)
              (Γ : gam) : D.d tags_t -> gam -> ienv -> Prop :=
    | chk_vardeclare (τ : E.t tags_t) (x : string tags_t) (i : tags_t) :
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
             E.equivt τ τ' /\ ⟦ errs , Γ ⟧ ⊢ e ∈ τ)
          cargs cparams ->
        let x' := bare x in
        ⦗ cs, fns, ins, errs, Γ ⦘ ⊢ Instance x of c(cargs) @ i ⊣ ⦗ Γ, x' ↦ params ;; ins ⦘
(* Functions belong only to the top-level declarations.
    | chk_function (f : name tags_t) (sig : E.arrowT tags_t)
                   (body : S.s tags_t) (i : tags_t)
                   (Γ' Γ'' : gam) (sg : signal) :
        bind_all sig Γ = Γ' ->
        (⦃ fns, errs, mkds, Γ' ⦄ ⊢ body ⊣ Γ'', sg) ->
        good_signal sig sg ->
        check_decl cs ins fns errs mkds Γ
                   (D.DFunction f sig body i) Γ !{ f ↦ sig ;; fns }! ins *)
    | chk_declseq (d1 d2 : D.d tags_t) (i : tags_t)
                  (ins' ins'' : ienv) (Γ' Γ'' : gam) :
        ⦗ cs, fns, ins,  errs, Γ  ⦘ ⊢ d1 ⊣ ⦗ Γ',  ins' ⦘ ->
        ⦗ cs, fns, ins', errs, Γ' ⦘ ⊢ d2 ⊣ ⦗ Γ'', ins'' ⦘ ->
        ⦗ cs, fns, ins,  errs, Γ  ⦘ ⊢ d1 ;; d2 @ i ⊣ ⦗ Γ'', ins'' ⦘
    where "⦗ cenv , fenv , ienv1 , errs , g1 ⦘ ⊢ d ⊣ ⦗ g2 , ienv2 ⦘"
            := (check_decl cenv fenv ienv1 errs g1 d g2 ienv2).
    (**[]*)
  End TypeCheck.
End Typecheck.
