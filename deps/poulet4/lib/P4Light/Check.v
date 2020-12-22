(** * Typechecking *)

Require Export P4Light.AST.

(** * Environments *)

(** Note how the type of the environment's domain
    is an argument to the environment functor. *)
Module Env (DOM : P4Data).
  Import DOM.
  Module DU := P4DataUtil DOM.
  Import DU.

  (** Definition of environments. *)
  Definition env (T : Type) : Type := t -> option T.

  (** The empty environment. *)
  Definition empty (T : Type) : env T := fun _ => None.

  Section EnvDefs.
    Context {T : Type}.

    (** Updating the environment. *)
    Definition bind (x : t) (v : T) (e : env T) : env T :=
      fun y => if x =? y then Some v else e y.

    (* TODO: whatever lemmas needed. *)
  End EnvDefs.

  Module EnvNotations.
    Declare Custom Entry p4env.

    Notation "x" := x (in custom p4env at level 0, x constr at level 0).

    Notation "x ↦ v ';;' e"
      := (bind x v e)
           (in custom p4env at level 40, e custom p4env,
               right associativity).
  End EnvNotations.
End Env.

(** * Typechecking *)
Module Typecheck (NAME : P4Data) (INT BIGINT : P4Numeric) (I : P4Info).
  Module IU := P4NumericUtil(INT).
  Infix "+" := IU.add (at level 50, left associativity).

  Module P := P4 NAME INT BIGINT I.

  Module E := P.Expr.
  Module S := P.Stmt.
  Module F := P.F.
  Definition dir := P.Dir.d.

  Import E.TypeNotations.
  Import E.ExprNotations.

  Module NM := Env NAME.
  Import NM.EnvNotations.

  (** Available error names. *)
  Definition errors : Type := NM.env unit.

  (** Available matchkinds. *)
  Definition matchkinds : Type := NM.env unit.

  (** Typing context. *)
  Definition gam : Type := NM.env E.t.

  Definition out_update (fs : F.fs (dir * (E.t * E.e))) : gam -> gam :=
    fs
      ▷ F.filter (fun '(d,_) =>
                     match d with
                     | P.Dir.DOut | P.Dir.DInOut => true
                     | _ => false end)
      ▷ F.fold (fun x '(_, (t,_)) acc => NM.bind x t acc).

  Reserved Notation "⟦ ers ',' mks ',' gm ⟧ ⊢ e ∈ t"
           (at level 40, e custom p4expr, t custom p4type at level 0).

  (** Expression typing as a relation. *)
  Inductive check (errs : errors) (mkds : matchkinds)
            (Γ : gam) : E.e -> E.t -> Prop :=
    (* Literals. *)
    | chk_bool (b : bool) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ BOOL b @ i ∈ Bool
    | chk_int (n : INT.t) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ Int n @ i ∈ int
    | chk_bitstring (w : INT.t) (v : BIGINT.t) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ Bit<w> v @ i ∈ bit<w>
    | chk_var (x : NAME.t) (τ : E.t) (i : I.t) :
        Γ x = Some τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ Var x :: τ @ i end ∈ τ
   (* Unary operations. *)
   | chk_not (e : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ Bool ->
       ⟦ errs , mkds , Γ ⟧ ⊢ ! e :: Bool @ i end ∈ Bool
   | chk_bitnot (w : INT.t) (e : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ bit<w> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ ~ e :: bit<w> @ i end ∈ bit<w>
   | chk_uminus (e : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ - e :: int @ i end ∈ int
   (* Binary Operations. *)
   | chk_plus (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ + e1 :: int e2 :: int @ i end ∈ int
   | chk_minus (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ -- e1 :: int e2 :: int @ i end ∈ int
   | chk_plussat (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ |+| e1 :: bit<n> e2 :: bit<n> @ i end ∈ bit<n>
   | chk_minussat (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ |-| e1 :: bit<n> e2 :: bit<n> @ i end ∈ bit<n>
   | chk_bitand (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ & e1 :: bit<n> e2 :: bit<n> @ i end ∈ bit<n>
   | chk_bitor (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ | e1 :: bit<n> e2 :: bit<n> @ i end ∈ bit<n>
   | chk_bitxor (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ ^ e1 :: bit<n> e2 :: bit<n> @ i end ∈ bit<n>
   | chk_and (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ Bool ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ Bool ->
       ⟦ errs , mkds , Γ ⟧ ⊢ && e1 :: Bool e2 :: Bool @ i end ∈ Bool
   | chk_or (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ Bool ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ Bool ->
       ⟦ errs , mkds , Γ ⟧ ⊢ || e1 :: Bool e2 :: Bool @ i end ∈ Bool
   | chk_le (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ <= e1 :: int e2 :: int @ i end ∈ Bool
   | chk_ge (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ >= e1 :: int e2 :: int @ i end ∈ Bool
   | chk_lt (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ < e1 :: int e2 :: int @ i end ∈ Bool
   | chk_gt (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ > e1 :: int e2 :: int @ i end ∈ Bool
   | chk_eq (τ : E.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ ->
       ⟦ errs , mkds , Γ ⟧ ⊢ == e1 :: τ e2 :: τ @ i end ∈ Bool
   | chk_neq (τ : E.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ τ ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ τ ->
       ⟦ errs , mkds , Γ ⟧ ⊢ != e1 :: τ e2 :: τ @ i end ∈ Bool
   | chk_shl (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ << e1 :: bit<n> e2 :: int @ i end ∈ bit<n>
   | chk_shr (n : INT.t) (e1 e2 : E.e) (i : I.t) :
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ int ->
       ⟦ errs , mkds , Γ ⟧ ⊢ >> e1 :: bit<n> e2 :: int @ i end ∈ bit<n>
   | chk_plusplus (m n w : INT.t) (e1 e2 : E.e) (i : I.t) :
       m + n = w ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e1 ∈ bit<m> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e2 ∈ bit<n> ->
       ⟦ errs , mkds , Γ ⟧ ⊢ ++ e1 :: bit<m> e2 :: bit<n> @ i end ∈ bit<w>
   (* Member expressions. *)
   | chk_hdr_mem (e : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (τ : E.t) (i : I.t) :
       In (x, τ) fields ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ hdr { fields } ->
       ⟦ errs , mkds , Γ ⟧ ⊢ Mem e :: hdr { fields } dot x @ i end ∈ τ
   | chk_rec_mem (e : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (τ : E.t) (i : I.t) :
       In (x, τ) fields ->
       ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ rec { fields } ->
       ⟦ errs , mkds , Γ ⟧ ⊢ Mem e :: rec { fields } dot x @ i end ∈ τ
   (* Records. *)
   | chk_rec_lit (efs : F.fs (E.t * E.e)) (tfs : F.fs E.t) (i : I.t) :
      F.relfs
        (fun te τ =>
           fst te = τ /\ let e := snd te in
           ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      ⟦ errs , mkds , Γ ⟧ ⊢ rec { efs } @ i ∈ rec { tfs }
   (* Errors and matchkinds. *)
   | chk_error (err : NAME.t) (i : I.t) :
       errs err = Some tt ->
       ⟦ errs , mkds , Γ ⟧ ⊢ Error err @ i ∈ error
   | chk_matchkind (mkd : NAME.t) (i : I.t) :
       mkds mkd = Some tt ->
       ⟦ errs , mkds , Γ ⟧ ⊢ Matchkind mkd @ i ∈ error
   where "⟦ ers ',' mks ',' gm ⟧ ⊢ ex ∈ ty"
           := (check ers mks gm ex ty).
  (**[]*)

  Import S.StmtNotations.

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

  (** Available functions. *)
  Definition fenv : Type := NM.env (E.arrowT).

  Reserved Notation "⦃ fe ',' errs ',' mks ',' g1 ⦄ ⊢ s ⊣ g2 ',' sg"
           (at level 40, s custom p4stmt,
            g2 custom p4env, sg custom p4signal).

  Inductive check_stmt (fns : fenv) (errs : errors)
            (mkds : matchkinds) (Γ : gam) : S.s -> gam -> signal -> Prop :=
    | chk_skip (i : I.t) :
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ skip @ i ⊣ Γ, C
    | chk_seq_cont (s1 s2 : S.s) (Γ' Γ'' : gam)
                   (i : I.t) (sig : signal) :
        ⦃ fns , errs , mkds , Γ  ⦄ ⊢ s1 ⊣ Γ', C ->
        ⦃ fns , errs , mkds , Γ' ⦄ ⊢ s2 ⊣ Γ'', sig ->
        ⦃ fns , errs , mkds , Γ  ⦄ ⊢ s1 ; s2 @ i ⊣ Γ'', sig
    | chk_seq_ret (s1 s2 : S.s) (Γ' : gam) (i : I.t) :
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ s1 ⊣ Γ', R ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ s1 ; s2 @ i ⊣ Γ', R
    | chk_vardecl (τ : E.t) (x : NAME.t)
                  (e : E.e) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ decl x ≜ e :: τ @ i fin ⊣ x ↦ τ ;; Γ, C
    | chk_assign (τ : E.t) (lhs rhs : E.e) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ lhs ∈ τ ->
        ⟦ errs , mkds , Γ ⟧ ⊢ rhs ∈ τ ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ asgn lhs := rhs :: τ @ i fin ⊣ Γ, C
    | chk_cond (τ : E.t) (guard : E.e) (tru fls : S.s)
               (Γ1 Γ2 : gam) (i : I.t) (sgt sgf sg : signal) :
        sg = lub sgt sgf ->
        ⟦ errs , mkds , Γ ⟧ ⊢ guard ∈ τ ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ tru ⊣ Γ1, sgt ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ fls ⊣ Γ2, sgf ->
        ⦃ fns , errs , mkds , Γ ⦄
          ⊢ if guard :: τ then tru else fls @ i fin ⊣ Γ, sg
    | chk_return_void (i : I.t) :
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ returns @ i ⊣ Γ, R
    | chk_return_fruit (τ : E.t) (e : E.e) (i : I.t) :
        ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ ->
        ⦃ fns , errs, mkds , Γ ⦄ ⊢ return e :: τ @ i fin ⊣ Γ, R
    | chk_method_call (Γ' : gam) (params : F.fs (dir * E.t))
                      (args : F.fs (dir * (E.t * E.e)))
                      (f : NAME.t) (i : I.t) :
        Γ' = out_update args Γ ->
        fns f = Some (E.Arrow E.t params None) ->
        F.relfs
          (fun dte dt =>
             fst dt = fst dte /\ snd dt = dte ▷ snd ▷ fst /\
             let e := dte ▷ snd ▷ snd in
             let τ := snd dt in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ)
          args params ->
        ⦃ fns , errs , mkds , Γ ⦄ ⊢ call f with args @ i fin ⊣ Γ', C
    | chk_call (Γ' : gam) (params : F.fs (dir * E.t))
               (τ : E.t) (args : F.fs (dir * (E.t * E.e)))
               (f x : NAME.t) (i : I.t) :
        Γ' = out_update args Γ ->
        fns f = Some (E.Arrow _ params (Some τ)) ->
        F.relfs
          (fun dte dt =>
             fst dt = fst dte /\ snd dt = dte ▷ snd ▷ fst /\
             let e := dte ▷ snd ▷ snd in
             let τ := snd dt in
             ⟦ errs , mkds , Γ ⟧ ⊢ e ∈ τ)
          args params ->
        ⦃ fns , errs , mkds , Γ ⦄
          ⊢ let x :: τ := call f with args @ i fin ⊣ x ↦ τ ;; Γ', C
    where "⦃ fe ',' ers ',' mks ',' g1 ⦄ ⊢ s ⊣ g2 ',' sg"
            := (check_stmt fe ers mks g1 s g2 sg).
  (**[]*)
End Typecheck.
