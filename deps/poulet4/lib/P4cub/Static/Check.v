Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.

(** Notation entries. *)
Declare Custom Entry p4signal.
Declare Custom Entry p4context.

(** Expression typing. *)
Reserved Notation "⟦ ers , gm ⟧ ⊢ e ∈ t"
         (at level 40, e custom p4expr, t custom p4type at level 0).

(** Statement typing. *)
Reserved Notation "⦃ fns , errs , g1 ⦄ ctx ⊢ s ⊣ ⦃ g2 , sg ⦄"
         (at level 40, s custom p4stmt, ctx custom p4context,
          g2 custom p4env, sg custom p4signal).

(** Parser-expression typing. *)
Reserved Notation "⟅ sts , ers , gm ⟆ ⊢ e" (at level 40, e custom p4prsrexpr).

(** Parser-state-block typing. *)
Reserved Notation "'⟅⟅' fns , pis , eis , sts , errs , Γ '⟆⟆' ⊢ s"
         (at level 40, s custom p4prsrstateblock).

(** Control-declaration typing. *)
Reserved Notation
         "⦅ ts1 , as1 , cs , fs , ci , ei , errs , g ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
         (at level 60, d custom p4ctrldecl,
          ts1 custom p4env, as1 custom p4env,
          ts2 custom p4env, as2 custom p4env).

(** Toplevel-declaration typing. *)
Reserved Notation
         "⦗ cs1 , fs1 , ci1 , pi1 , ei1 , ers , g1 ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , fs2 , cs2 ⦘"
         (at level 70, d custom p4topdecl, ei2 custom p4env, pi2 custom p4env,
          ci2 custom p4env, fs2 custom p4env, cs2 custom p4env).

(** * Typechecking *)
Module Typecheck.
  Module P := P4cub.

  Module E := P.Expr.
  Import E.TypeEquivalence.
  Module PT := E.ProperType.

  Module ST := P.Stmt.
  Module PR := P.Parser.
  Module CD := P.Control.ControlDecl.
  Module TD := P.TopDecl.
  Module F := P.F.
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

  Module TypeCheckDefs.
    (** Available strings. *)
    Definition strs : Type := Env.t string unit.

    (** Available error names. *)
    Definition errors : Type := strs.

    (** Typing context. *)
    Definition gamma : Type := Env.t string E.t.

    (** Evidence for a type being a numeric of a given width. *)
    Inductive numeric_width (w : positive) : E.t -> Prop :=
    | numeric_width_bit : numeric_width w {{ bit<w> }}
    | numeric_width_int : numeric_width w {{ int<w> }}.

    Ltac inv_numeric_width :=
      match goal with
      | H: numeric_width _ _ |- _ => inv H
      end.
    (**[]*)

    (** Evidence for a type being numeric. *)
    Inductive numeric : E.t -> Prop :=
      Numeric (w : positive) (τ : E.t) :
        numeric_width w τ -> numeric τ.
    (**[]*)

    Ltac inv_numeric :=
      match goal with
      | H: numeric _ |- _ => inv H; try inv_numeric_width
      end.
    (**[]*)

    (** Evidence a unary operation is valid for a type. *)
    Inductive uop_type : E.uop -> E.t -> E.t -> Prop :=
    | UTBool :
        uop_type _{ ! }_ {{ Bool }} {{ Bool }}
    | UTBitNot τ :
        numeric τ -> uop_type _{ ~ }_ τ τ
    | UTUMinus τ :
        numeric τ -> uop_type _{ - }_ τ τ
    | UTIsValid ts :
        uop_type _{ isValid }_ {{ hdr { ts } }} {{ Bool }}
    | UTSetValid ts :
        uop_type _{ setValid }_ {{ hdr { ts } }} {{ hdr { ts } }}
    | UTSetInValid ts :
        uop_type _{ setInValid }_ {{ hdr { ts } }} {{ hdr { ts } }}
    | UTNext ts n :
        uop_type _{ Next }_ {{ stack ts[n] }} {{ hdr { ts } }}
    | UTSize ts n :
        let w := 32%positive in
        uop_type _{ Size }_ {{ stack ts[n] }} {{ bit<w> }}
    | UTPush ts n p :
        uop_type _{ Push p }_ {{ stack ts[n] }} {{ stack ts[n] }}
    | UTPop ts n p :
        uop_type _{ Pop  p }_ {{ stack ts[n] }} {{ stack ts[n] }}.
    (**[]*)

    (** Evidence a binary operation is valid
        for operands of a type and produces some type. *)
    Inductive bop_type : E.bop -> E.t -> E.t -> E.t -> Prop :=
    | BTPlus τ : numeric τ -> bop_type +{ + }+ τ τ τ
    | BTPlusSat τ : numeric τ -> bop_type +{ |+| }+ τ τ τ
    | BTMinus τ : numeric τ -> bop_type +{ - }+ τ τ τ
    | BTMinusSat τ : numeric τ -> bop_type +{ |-| }+ τ τ τ
    | BTTimes τ : numeric τ -> bop_type +{ × }+ τ τ τ
    | BTShl τ1 w2 : numeric τ1 -> bop_type +{ << }+ τ1 {{ bit<w2> }} τ1
    | BTShr τ1 w2 : numeric τ1 -> bop_type +{ >> }+ τ1 {{ bit<w2> }} τ1
    | BTBitAnd τ : numeric τ -> bop_type +{ & }+ τ τ τ
    | BTBitXor τ : numeric τ -> bop_type +{ ^ }+ τ τ τ
    | BTBitOr τ : numeric τ -> bop_type +{ | }+ τ τ τ
    | BTLe τ : numeric τ -> bop_type +{ <= }+ τ τ {{ Bool }}
    | BTLt τ : numeric τ -> bop_type +{ < }+ τ τ {{ Bool }}
    | BTGe τ : numeric τ -> bop_type +{ >= }+ τ τ {{ Bool }}
    | BTGt τ : numeric τ -> bop_type +{ > }+ τ τ {{ Bool }}
    | BTAnd : bop_type +{ && }+ {{ Bool }} {{ Bool }} {{ Bool }}
    | BTOr : bop_type +{ || }+ {{ Bool }} {{ Bool }} {{ Bool }}
    | BTEq τ : bop_type +{ == }+ τ τ {{ Bool }}
    | BTNotEq τ : bop_type +{ != }+ τ τ {{ Bool }}
    | BTPlusPlusBit w1 w2 w τ2 :
        (w1 + w2)%positive = w ->
        numeric_width w2 τ2 ->
        bop_type +{ ++ }+ {{ bit<w1> }} τ2 {{ bit<w> }}
    | BTPlusPlusInt w1 w2 w τ2 :
        (w1 + w2)%positive = w ->
        numeric_width w2 τ2 ->
        bop_type +{ ++ }+ {{ int<w1> }} τ2 {{ int<w> }}.
    (**[]*)

    (** Evidence an error is ok. *)
    Inductive error_ok (errs : errors) : option string -> Prop :=
    | NoErrorOk : error_ok errs None
    | ErrorOk (x : string) :
        errs x = Some tt ->
        error_ok errs (Some x).
    (**[]*)

    (** Evidence a cast is proper. *)
    Inductive proper_cast : E.t -> E.t -> Prop :=
    | pc_bool_bit : proper_cast {{ Bool }} {{ bit<xH> }}
    | pc_bit_bool : proper_cast {{ bit<xH> }} {{ Bool }}
    | pc_bit_int (w : positive) : proper_cast {{ bit<w> }} {{ int<w> }}
    | pc_int_bit (w : positive) : proper_cast {{ int<w> }} {{ bit<w> }}
    | pc_bit_bit (w1 w2 : positive) : proper_cast {{ bit<w1> }} {{ bit<w2> }}
    | pc_int_int (w1 w2 : positive) : proper_cast {{ int<w1> }} {{ int<w2> }}
    | pc_tuple_rec (ts : list E.t) (fs : F.fs string E.t) :
        ts = F.values fs ->
        proper_cast {{ tuple ts }} {{ rec { fs } }}
    | pc_tuple_hdr (ts : list E.t) (fs : F.fs string E.t) :
        ts = F.values fs ->
        Forall PT.proper_inside_header ts ->
        proper_cast {{ tuple ts }} {{ hdr { fs } }}.
    (**[]*)

    (** Evidence member operations are valid on a type. *)
    Inductive member_type : F.fs string E.t -> E.t -> Prop :=
    | mt_rec ts : member_type ts {{ rec { ts } }}
    | mt_hdr ts : member_type ts {{ hdr { ts } }}.
    (**[]*)

    (** Available functions. *)
    Definition fenv : Type := Env.t string E.arrowT.

    (** Available actions. *)
    Definition aenv : Type := Env.t string E.params.

    (** Control Instance environment. *)
    Definition cienv : Type := Env.t string E.params.

    (** Parser Instance environment. *)
    Definition pienv : Type := Env.t string E.params.

    (** Available extern instances. *)
    Definition eienv : Type := Env.t string (F.fs string E.arrowT).

    (** Available table names. *)
    Definition tblenv : Type := strs.

    (** Statement context. *)
    Inductive ctx : Type :=
    | CAction (available_actions : aenv)
              (available_externs : eienv) (* action block *)
    | CVoid (* void function *)
    | CFunction (return_type : E.t) (* fruitful function *)
    | CApplyBlock (tables : tblenv)
                  (available_actions : aenv)
                  (available_controls : cienv)
                  (available_externs : eienv) (* control apply block *)
    | CParserState (available_parsers : pienv)
                   (available_externs : eienv) (* parser state *).
    (**[]*)

    (** Evidence an extern method call context is ok. *)
    Inductive extern_call_ok (eis : eienv) : ctx -> Prop :=
    | extern_action_ok {aa : aenv} :
        extern_call_ok eis (CAction aa eis)
    | extern_apply_block_ok {tbls : tblenv} {aa : aenv} {cis : cienv} :
        extern_call_ok eis (CApplyBlock tbls aa cis eis)
    | extern_parser_state_ok {pis : pienv} :
        extern_call_ok eis (CParserState pis eis).
    (**[]*)

    (** Evidence an action call context is ok. *)
    Inductive action_call_ok
              (aa : aenv) : ctx -> Prop :=
    | action_action_ok {eis : eienv} :
        action_call_ok aa (CAction aa eis)
    | action_apply_block_ok {tbls : tblenv} {cis : cienv} {eis : eienv} :
        action_call_ok aa (CApplyBlock tbls aa cis eis).
    (**[]*)

    (** Evidence an exit context ok. *)
    Inductive exit_ctx_ok : ctx -> Prop :=
    | exit_action_ok {aa : aenv} {eis : eienv} :
        exit_ctx_ok (CAction aa eis)
    | exit_applyblk_ok {tbls : tblenv} {aa : aenv}
                       {cis : cienv} {eis : eienv} :
        exit_ctx_ok (CApplyBlock tbls aa cis eis).
    (**[]*)

    (** Evidence a void return is ok. *)
    Inductive return_void_ok : ctx -> Prop :=
    | return_void_action {aa : aenv} {eis : eienv} :
        return_void_ok (CAction aa eis)
    | return_void_void :
        return_void_ok CVoid
    | return_void_applyblk {tbls : tblenv} {aa : aenv}
                           {cis : cienv} {eis : eienv} :
        return_void_ok (CApplyBlock tbls aa cis eis).
    (**[]*)

    (** Available Constructors and their signatures. *)
    Definition cenv : Type := Env.t string E.ct.

    (** Put parameters into environment. *)
    Definition bind_all : E.params -> gamma -> gamma :=
      F.fold (fun x '(P.PAIn τ | P.PAOut τ | P.PAInOut τ) Γ => !{ x ↦ τ ;; Γ }!).
    (**[]*)

    (** Put (constructor) parameters into environments. *)
    Definition cbind_all :
      E.constructor_params  ->
      gamma * cienv * pienv * eienv -> gamma * cienv * pienv * eienv :=
      F.fold (fun x c '(Γ, cins, pins, eins) =>
                match c with
                | E.CTType τ => (!{ x ↦ τ;; Γ }!, cins, pins, eins)
                | E.CTControl _ pars => (Γ, !{ x ↦ pars;; cins }!, pins, eins)
                | E.CTParser _  pars => (Γ, cins, !{ x ↦ pars;; pins }!, eins)
                | E.CTExtern _  mhds => (Γ, cins, pins, !{ x ↦ mhds;; eins }!)
                end).
    (**[]*)

    (** Environment of user-defined parser states. *)
    Definition user_states : Type := strs.

    (** Valid parser states. *)
    Inductive valid_state (us : user_states) : PR.state -> Prop :=
    | start_valid :
        valid_state us ={ start }=
    | accept_valid :
        valid_state us ={ accept }=
    | reject_valid :
        valid_state us ={ reject }=
    | name_valid (st : string) :
        us st = Some tt ->
        valid_state us ={ δ st }=.
    (**[]*)
  End TypeCheckDefs.
  Export TypeCheckDefs.

  (** Appropriate signal. *)
  Inductive good_signal : E.arrowT -> signal -> Prop :=
  | good_signal_cont params :
      good_signal (P.Arrow params None) SIG_Cont
  | good_signal_return params ret :
      good_signal (P.Arrow params (Some ret)) SIG_Return.
  (**[]*)

  Notation "x" := x (in custom p4context at level 0, x constr at level 0).
  Notation "'Action' aa eis"
    := (CAction aa eis)
         (in custom p4context at level 0,
             aa custom p4env, eis custom p4env).
  Notation "'Void'" := CVoid (in custom p4context at level 0).
  Notation "'Function' t"
    := (CFunction t)
         (in custom p4context at level 0, t custom p4type).
  Notation "'ApplyBlock' tbls aa cis eis"
    := (CApplyBlock tbls aa cis eis)
         (in custom p4context at level 0, tbls custom p4env,
             aa custom p4env, cis custom p4env, eis custom p4env).
  Notation "'Parser' pis eis"
    := (CParserState pis eis)
         (in custom p4context at level 0,
             pis custom p4env, eis custom p4env).

  (** Expression typing as a relation. *)
  Inductive check_expr
            {tags_t : Type} (errs : errors) (Γ : gamma)
    : E.e tags_t -> E.t -> Prop :=
  (* Literals. *)
  | chk_bool (b : bool) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ BOOL b @ i ∈ Bool
  | chk_bit (w : positive) (n : Z) (i : tags_t) :
      BitArith.bound w n ->
      ⟦ errs , Γ ⟧ ⊢ w W n @ i ∈ bit<w>
  | chk_int (w : positive) (n : Z) (i : tags_t) :
      IntArith.bound w n ->
      ⟦ errs , Γ ⟧ ⊢ w S n @ i ∈ int<w>
  | chk_var (x : string) (τ : E.t) (i : tags_t) :
      Γ x = Some τ ->
      PT.proper_nesting τ ->
      ⟦ errs , Γ ⟧ ⊢ Var x:τ @ i ∈ τ
  | chk_slice (e : E.e tags_t) (τ : E.t)
              (hi lo w : positive) (i : tags_t) :
      (lo <= hi < w)%positive ->
      numeric_width w τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      let w' := (hi - lo + 1)%positive in
      ⟦ errs, Γ ⟧ ⊢ Slice e:τ [hi:lo] @ i ∈ bit<w'>
  | chk_cast (τ τ' : E.t) (e : E.e tags_t) (i : tags_t) :
      proper_cast τ' τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ' ->
      ⟦ errs, Γ ⟧ ⊢ Cast e:τ @ i ∈ τ
  (* Unary operations. *)
  | chk_uop (op : E.uop) (τ τ' : E.t) (e : E.e tags_t) (i : tags_t) :
      uop_type op τ τ' ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⟦ errs, Γ ⟧ ⊢ UOP op e:τ @ i ∈ τ'
  (* Binary Operations. *)
  | chk_bop (op : E.bop) (τ1 τ2 τ : E.t) (e1 e2 : E.e tags_t) (i : tags_t) :
      bop_type op τ1 τ2 τ ->
      ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ1 ->
      ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ2 ->
      ⟦ errs , Γ ⟧ ⊢ BOP e1:τ1 op e2:τ2 @ i ∈ τ
  (* Member expressions. *)
  | chk_mem (e : E.e tags_t) (x : string)
            (fs : F.fs string E.t)
            (τ τ' : E.t) (i : tags_t) :
      F.get x fs = Some τ' ->
      member_type fs τ ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⟦ errs, Γ ⟧ ⊢ Mem e:τ dot x @ i ∈ τ'
  (* Structs. *)
  | chk_tuple (es : list (E.e tags_t)) (i : tags_t)
              (ts : list E.t) :
      Forall2 (fun e τ => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es ts ->
      ⟦ errs, Γ ⟧ ⊢ tup es @ i ∈ tuple ts
  | chk_rec_lit (efs : F.fs string (E.t * E.e tags_t))
                (tfs : F.fs string E.t) (i : tags_t) :
      F.relfs
        (fun te τ =>
           (fst te) = τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      ⟦ errs , Γ ⟧ ⊢ rec { efs } @ i ∈ rec { tfs }
  | chk_hdr_lit (efs : F.fs string (E.t * E.e tags_t))
                (tfs : F.fs string E.t)
                (i : tags_t) (b : E.e tags_t) :
      PT.proper_nesting {{ hdr { tfs } }} ->
      F.relfs
        (fun te τ =>
           (fst te) = τ /\
           let e := snd te in
           ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
      ⟦ errs, Γ ⟧ ⊢ b ∈ Bool ->
      ⟦ errs , Γ ⟧ ⊢ hdr { efs } valid := b @ i ∈ hdr { tfs }
  (* Errors and matchkinds. *)
  | chk_error (err : option string) (i : tags_t) :
      error_ok errs err ->
      ⟦ errs , Γ ⟧ ⊢ Error err @ i ∈ error
  | chk_matchkind (mkd : E.matchkind) (i : tags_t) :
      ⟦ errs , Γ ⟧ ⊢ Matchkind mkd @ i ∈ matchkind
  (* Header stacks. *)
  | chk_stack (ts : F.fs string E.t)
              (hs : list (E.e tags_t))
              (n : positive) (ni : Z) (i : tags_t) :
      BitArith.bound 32%positive (Zpos n) ->
      (0 <= ni < (Zpos n))%Z ->
      Pos.to_nat n = length hs ->
      PT.proper_nesting {{ stack ts[n] }} ->
      Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
      ⟦ errs, Γ ⟧ ⊢ Stack hs:ts[n] nextIndex:=ni @ i ∈ stack ts[n]
  | chk_access (e : E.e tags_t) (idx : Z) (i : tags_t)
               (ts : F.fs string E.t) (n : positive) :
      (0 <= idx < (Zpos n))%Z ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ stack ts[n] ->
      ⟦ errs, Γ ⟧ ⊢ Access e[idx] @ i ∈ hdr { ts }
  where "⟦ ers ',' gm ⟧ ⊢ e ∈ ty"
          := (check_expr ers gm e ty) : type_scope.
  (**[]*)

  (** Custom induction principle for expression typing. *)
  Section CheckExprInduction.
    Variable (tags_t : Type).

    (** An arbitrary predicate. *)
    Variable P : errors -> gamma -> E.e tags_t -> E.t -> Prop.

    Hypothesis HBool : forall errs Γ b i,
      P errs Γ <{ BOOL b @ i }> {{ Bool }}.
    (**[]*)

    Hypothesis HBit : forall errs Γ w n i,
        BitArith.bound w n ->
        P errs Γ <{ w W n @ i }> {{ bit<w> }}.
    (**[]*)

    Hypothesis HInt : forall errs Γ w z i,
        IntArith.bound w z ->
        P errs Γ <{ w S z @ i }> {{ int<w> }}.
    (**[]*)

    Hypothesis HVar : forall errs Γ x τ i,
        Γ x = Some τ ->
        PT.proper_nesting τ ->
        P errs Γ <{ Var x:τ @ i }> τ.
    (**[]*)

    Hypothesis HSlice : forall errs Γ e τ hi lo w i,
        (lo <= hi < w)%positive ->
        numeric_width w τ ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        P errs Γ e τ ->
        let w' := (hi - lo + 1)%positive in
        P errs Γ <{ Slice e:τ [hi:lo] @ i }> {{ bit<w'> }}.
    (**[]*)

    Hypothesis HCast : forall errs Γ τ τ' e i,
        proper_cast τ' τ ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ' ->
        P errs Γ e τ' ->
        P errs Γ <{ Cast e:τ @ i }> τ.
    (**[]*)

    Hypothesis HUop : forall errs Γ op τ τ' e i,
        uop_type op τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        P errs Γ e τ ->
        P errs Γ <{ UOP op e:τ @ i }> τ'.

    Hypothesis HBop : forall errs Γ op τ1 τ2 τ e1 e2 i,
        bop_type op τ1 τ2 τ ->
        ⟦ errs , Γ ⟧ ⊢ e1 ∈ τ1 ->
        P errs Γ e1 τ1 ->
        ⟦ errs , Γ ⟧ ⊢ e2 ∈ τ2 ->
        P errs Γ e2 τ2 ->
        P errs Γ <{ BOP e1:τ1 op e2:τ2 @ i }> τ.

    Hypothesis HMem : forall errs Γ e x fs τ τ' i,
        F.get x fs = Some τ' ->
        member_type fs τ ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        P errs Γ e τ ->
        P errs Γ <{ Mem e:τ dot x @ i }> τ'.
    (**[]*)

    Hypothesis HTuple : forall errs Γ es i ts,
        Forall2 (fun e τ => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es ts ->
        Forall2 (P errs Γ) es ts ->
        P errs Γ <{ tup es @ i }> {{ tuple ts }}.
    (**[]*)

    Hypothesis HRecLit : forall errs Γ efs tfs i,
        F.relfs
          (fun te τ =>
             (fst te) = τ /\
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
             (fst te) = τ /\
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

    Hypothesis HStack : forall errs Γ ts hs n ni i,
        BitArith.bound 32%positive (Zpos n) ->
        (0 <= ni < (Zpos n))%Z ->
        Pos.to_nat n = length hs ->
        PT.proper_nesting {{ stack ts[n] }} ->
        Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
        Forall (fun e => P errs Γ e {{ hdr { ts } }}) hs ->
        P errs Γ <{ Stack hs:ts[n] nextIndex:=ni @ i }> {{ stack ts[n] }}.
    (**[]*)

    Hypothesis HAccess : forall errs Γ e idx i ts n,
        (0 <= idx < (Zpos n))%Z ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ stack ts[n] ->
        P errs Γ e {{ stack ts[n] }} ->
        P errs Γ <{ Access e[idx] @ i }> {{ hdr { ts } }}.
    (**[]*)

    (** Custom induction principle for expression typing.
        Do [induction ?H using custom_check_expr_ind]. *)
    Definition custom_check_expr_ind :
      forall (errs : errors) (Γ : gamma) (e : E.e tags_t) (τ : E.t)
        (HY : ⟦ errs, Γ ⟧ ⊢ e ∈ τ), P errs Γ e τ :=
          fix chind errs Γ e τ HY :=
            let fix lind
                    {es : list (E.e tags_t)}
                    {ts : list E.t}
                    (HR : Forall2 (fun e τ => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es ts)
                : Forall2 (P errs Γ) es ts :=
                match HR with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons _ _ Hh Htail
                  => Forall2_cons _ _ (chind _ _ _ _ Hh) (lind Htail)
                end in
            let fix lind_stk
                    {es : list (E.e tags_t)} {τ : E.t}
                    (HRs : Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) es)
                : Forall (fun e => P errs Γ e τ) es :=
                match HRs with
                | Forall_nil _ => Forall_nil _
                | Forall_cons _ Hhead Htail
                  => Forall_cons _ (chind _ _ _ _ Hhead) (lind_stk Htail)
                end in
            let fix fields_ind
                    {efs : F.fs string (E.t * E.e tags_t)}
                    {tfs : F.fs string E.t}
                    (HRs : F.relfs
                             (fun te τ =>
                                (fst te) = τ /\
                                let e := snd te in
                                ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs)
                : F.relfs
                    (fun te τ => let e := snd te in P errs Γ e τ)
                    efs tfs :=
                match HRs with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons te τ (conj HName (conj _ Hhead)) Htail
                  => Forall2_cons te τ
                                 (conj HName (chind errs Γ _ _ Hhead))
                                 (fields_ind Htail)
                end in
            match HY with
            | chk_bool _ _ b i     => HBool errs Γ b i
            | chk_bit _ _ _ _ H i => HBit _ _ _ _ H i
            | chk_int _ _ _ _ H i => HInt _ _ _ _ H i
            | chk_var _ _ _ _ i HP HV => HVar _ _ _ _ i HP HV
            | chk_slice _ _ _ _ _ _ _ i Hlohiw Ht He
              => HSlice _ _ _ _ _ _ _ i Hlohiw Ht He (chind _ _ _ _ He)
            | chk_cast _ _ _ _ _ i HPC He
              => HCast _ _ _ _ _ i HPC He (chind _ _ _ _ He)
            | chk_uop _ _ _ _ _ _ i Huop He
              => HUop _ _ _ _ _ _ i Huop He (chind _ _ _ _ He)
            | chk_bop _ _ _ _ _ _ _ _ i Hbop He1 He2
              => HBop _ _ _ _ _ _ _ _ i Hbop
                     He1 (chind _ _ _ _ He1)
                     He2 (chind _ _ _ _ He2)
            | chk_mem _ _ _ _ _ _ _ _ i Hget He
              => HMem _ _ _ _ _ _ _ _ i Hget He (chind _ _ _ _ He)
            | chk_error _ _ _ i HOK => HError errs Γ _ i HOK
            | chk_matchkind _ _ mk i  => HMatchKind errs Γ mk i
            | chk_tuple _ _ _ i _ HR => HTuple _ _ _ i _ HR (lind HR)
            | chk_rec_lit _ _ _ _ i HRs
              => HRecLit _ _ _ _ i HRs (fields_ind HRs)
            | chk_hdr_lit _ _ _ _ i _ HP HRs Hb
              => HHdrLit _ _ _ _ i _ HP
                        HRs (fields_ind HRs)
                        Hb (chind _ _ _ _ Hb)
            | chk_stack _ _ _ _ _ _ i Hn Hni Hlen HP HRs
              => HStack _ _ _ _ _ _ i Hn Hni Hlen HP HRs (lind_stk HRs)
            | chk_access _ _ _ _ i _ _ Hidx He
              => HAccess _ _ _ _ i _ _ Hidx He (chind _ _ _ _ He)
            end.
     (**[]*)
  End CheckExprInduction.

  (** (Syntactic) Evidence an expression may be an lvalue. *)
  Inductive lvalue_ok {tags_t : Type} : E.e tags_t -> Prop :=
  | lvalue_var x τ i : lvalue_ok <{ Var x:τ @ i }>
  | lvalue_member e τ x i :
      lvalue_ok e ->
      lvalue_ok <{ Mem e:τ dot x @ i }>
  | lvalue_access e idx i :
      lvalue_ok e ->
      lvalue_ok <{ Access e[idx] @ i }>.
  (**[]*)

  (** Select-pattern-typing. *)
  Inductive check_pat : PR.pat -> E.t -> Prop :=
  | chk_wild t : check_pat [{ ?? }] t
  | chk_mask p1 p2 w :
      check_pat p1 {{ bit<w> }} ->
      check_pat p2 {{ bit<w> }} ->
      check_pat [{ p1 &&& p2 }] {{ bit<w> }}
  | chk_range p1 p2 w :
      check_pat p1 {{ bit<w> }} ->
      check_pat p2 {{ bit<w> }} ->
      check_pat [{ p1 .. p2 }] {{ bit<w> }}
  | chk_pbit w n :
      check_pat [{ w PW n }] {{ bit<w> }}
  | chk_pint w z :
      check_pat [{ w PS z }] {{ int<w> }}
  | chk_ptup ps ts :
      Forall2 check_pat ps ts ->
      check_pat [{ PTUP ps }] {{ tuple ts }}.
  (**[]*)

  Section PatternCheckInduction.
    Variable P : PR.pat -> E.t -> Prop.

    Hypothesis HWild : forall t, P [{ ?? }] t.

    Hypothesis HMask : forall p1 p2 w,
        check_pat p1 {{ bit<w> }} ->
        P p1 {{ bit<w> }} ->
        check_pat p2 {{ bit<w> }} ->
        P p2 {{ bit<w> }} ->
        P [{ p1 &&& p2 }] {{ bit<w> }}.

    Hypothesis HRange : forall p1 p2 w,
        check_pat p1 {{ bit<w> }} ->
        P p1 {{ bit<w> }} ->
        check_pat p2 {{ bit<w> }} ->
        P p2 {{ bit<w> }} ->
        P [{ p1 .. p2 }] {{ bit<w> }}.

    Hypothesis HBit : forall w n, P [{ w PW n }] {{ bit<w> }}.

    Hypothesis HInt : forall w z, P [{ w PS z }] {{ int<w> }}.

    Hypothesis HTuple : forall ps ts,
        Forall2 check_pat ps ts ->
        Forall2 P ps ts ->
        P [{ PTUP ps }] {{ tuple ts }}.

    Definition custom_check_pat_ind : forall p t,
        check_pat p t -> P p t :=
      fix pind p t (H : check_pat p t) :=
        let fix lind {ps : list PR.pat} {ts : list E.t}
                 (H : Forall2 check_pat ps ts) : Forall2 P ps ts :=
            match H with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hh Ht
              => Forall2_cons _ _ (pind _ _ Hh) (lind Ht)
            end in
        match H with
        | chk_wild _ => HWild _
        | chk_mask _ _ _ Hp1 Hp2
          => HMask _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
        | chk_range _ _ _ Hp1 Hp2
          => HRange _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
        | chk_pbit w n => HBit w n
        | chk_pint w z => HInt w z
        | chk_ptup _ _ H => HTuple _ _ H (lind H)
        end.
    (**[]*)
  End PatternCheckInduction.
                           
  (** Parser-expression typing. *)
  Inductive check_prsrexpr {tags_t : Type}
            (sts : user_states) (errs : errors) (Γ : gamma)
    : PR.e tags_t -> Prop :=
  | chk_goto (st : PR.state) (i : tags_t) :
      valid_state sts st ->
      ⟅ sts, errs, Γ ⟆ ⊢ goto st @ i
  | chk_select (e : E.e tags_t) (def : PR.e tags_t)
               (cases : F.fs PR.pat (PR.e tags_t))
               (i : tags_t) (τ : E.t) :
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⟅ sts, errs, Γ ⟆ ⊢ def ->
      Forall
        (fun pe =>
           let p := fst pe in
           let e := snd pe in
           check_pat p τ /\ ⟅ sts, errs, Γ ⟆ ⊢ e) cases ->
      ⟅ sts, errs, Γ ⟆ ⊢ select e { cases } default:=def @ i
  where "⟅ sts , ers , gm ⟆ ⊢ e"
          := (check_prsrexpr sts ers gm e).
  (**[]*)

  (** A custom induction principle for parser-expression typing. *)
  Section CheckParserExprInduction.
    Variable tags_t: Type.

    (** An arbitrary predicate. *)
    Variable P : user_states -> errors -> gamma -> PR.e tags_t -> Prop.

    Hypothesis HGoto : forall sts errs Γ st i,
        valid_state sts st ->
        P sts errs Γ p{ goto st @ i }p.

    Hypothesis HSelect : forall sts errs Γ e def cases i τ,
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        ⟅ sts, errs, Γ ⟆ ⊢ def ->
        P sts errs Γ def ->
        Forall
          (fun pe =>
             let p := fst pe in
             let e := snd pe in
             check_pat p τ /\ ⟅ sts, errs, Γ ⟆ ⊢ e) cases ->
        F.predfs_data (P sts errs Γ) cases ->
        P sts errs Γ p{ select e { cases } default:=def @ i }p.

    (** Custom induction principle.
        Do [induction ?H using custom_check_prsrexpr_ind] *)
    Definition custom_check_prsrexpr_ind :
      forall (sts : user_states) (errs : errors) (Γ : gamma) (e : PR.e tags_t)
        (Hy : ⟅ sts, errs, Γ ⟆ ⊢ e), P sts errs Γ e :=
      fix chind sts errs Γ e Hy :=
        let fix lind
                {cases : F.fs PR.pat (PR.e tags_t)} {τ : E.t}
                (HR : Forall
                        (fun pe =>
                           let p := fst pe in
                           let e := snd pe in
                           check_pat p τ /\ ⟅ sts, errs, Γ ⟆ ⊢ e) cases)
            : F.predfs_data (P sts errs Γ) cases :=
            match HR with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ (conj _ He) Htail
              => Forall_cons _ (chind _ _ _ _ He) (lind Htail)
            end in
        match Hy with
        | chk_goto _ _ _ _ Hst i => HGoto _ _ _ _ Hst i
        | chk_select _ _ _ _ _ _ i _
                     He Hd Hcases
          => HSelect _ _ _ _ _ _ i _ He Hd (chind _ _ _ _ Hd) Hcases (lind Hcases)
        end.
    (**[]*)
  End CheckParserExprInduction.
  
  (** Statement typing. *)
  Inductive check_stmt
            {tags_t : Type} (fns : fenv) (errs : errors) (Γ : gamma)
    : ctx -> ST.s tags_t -> gamma -> signal -> Prop :=
  | chk_skip (i : tags_t) (con : ctx) :
      ⦃ fns, errs, Γ ⦄ con ⊢ skip @ i ⊣ ⦃ Γ, C ⦄
  | chk_seq_cont (s1 s2 : ST.s tags_t) (Γ' Γ'' : gamma)
                 (i : tags_t) (sig : signal) (con : ctx) :
      ⦃ fns, errs, Γ  ⦄ con ⊢ s1 ⊣ ⦃ Γ', C ⦄ ->
      ⦃ fns, errs, Γ' ⦄ con ⊢ s2 ⊣ ⦃ Γ'', sig ⦄ ->
      ⦃ fns, errs, Γ  ⦄ con ⊢ s1 ; s2 @ i ⊣ ⦃ Γ'', sig ⦄
  | chk_block (s : ST.s tags_t) (Γ' : gamma) (sig : signal) (con : ctx) :
      ⦃ fns, errs, Γ ⦄ con ⊢ s ⊣ ⦃ Γ', sig ⦄ ->
      ⦃ fns, errs, Γ ⦄ con ⊢ b{ s }b ⊣ ⦃ Γ, C ⦄
  | chk_vardecl (τ : E.t) (x : string) (i : tags_t) (con : ctx) :
      ⦃ fns, errs, Γ ⦄ con ⊢ var x:τ @ i ⊣ ⦃ x ↦ τ ;; Γ, C ⦄
  | chk_assign (τ : E.t) (e1 e2 : E.e tags_t) (i : tags_t) (con : ctx) :
      lvalue_ok e1 ->
      ⟦ errs, Γ ⟧ ⊢ e1 ∈ τ ->
      ⟦ errs, Γ ⟧ ⊢ e2 ∈ τ ->
      ⦃ fns, errs, Γ ⦄ con ⊢ asgn e1 := e2 : τ @ i ⊣ ⦃ Γ, C ⦄
  | chk_cond (guard : E.e tags_t) (tru fls : ST.s tags_t)
             (Γ1 Γ2 : gamma) (i : tags_t) (sgt sgf sg : signal) (con : ctx) :
      lub sgt sgf = sg ->
      ⟦ errs, Γ ⟧ ⊢ guard ∈ Bool ->
      ⦃ fns, errs, Γ ⦄ con ⊢ tru ⊣ ⦃ Γ1, sgt ⦄ ->
      ⦃ fns, errs, Γ ⦄ con ⊢ fls ⊣ ⦃ Γ2, sgf ⦄ ->
      ⦃ fns, errs, Γ ⦄
        con ⊢ if guard:Bool then tru else fls @ i ⊣ ⦃ Γ, sg ⦄
  | chk_return_void (i : tags_t) (con : ctx) :
      return_void_ok con ->
      ⦃ fns, errs, Γ ⦄ con ⊢ returns @ i ⊣ ⦃ Γ, R ⦄
  | chk_return_fruit (τ : E.t) (e : E.e tags_t) (i : tags_t) :
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⦃ fns, errs, Γ ⦄ Function τ ⊢ return e:τ @ i ⊣ ⦃ Γ, R ⦄
  | chk_exit (i : tags_t) (con : ctx) :
      exit_ctx_ok con ->
      ⦃ fns, errs, Γ ⦄ con ⊢ exit @ i ⊣ ⦃ Γ, R ⦄
  | chk_void_call (params : E.params)
                  (args : E.args tags_t)
                  (f : string) (i : tags_t) (con : ctx) :
      fns f = Some (P.Arrow params None) ->
      F.relfs
        (P.rel_paramarg_same
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ))
        args params ->
      ⦃ fns, errs, Γ ⦄ con ⊢ call f with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_act_call (params : E.params)
                 (args : E.args tags_t)
                 (a : string) (i : tags_t)
                 (aa : aenv) (con : ctx) :
      action_call_ok aa con ->
      aa a = Some params ->
      F.relfs
        (P.rel_paramarg
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
        args params ->
      ⦃ fns, errs, Γ ⦄ con ⊢ calling a with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_fun_call (τ : E.t) (e : E.e tags_t)
                 (params : E.params)
                 (args : E.args tags_t)
                 (f : string) (i : tags_t) (con : ctx) :
      fns f = Some (P.Arrow params (Some τ)) ->
      F.relfs
        (P.rel_paramarg
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
        args params ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ⦃ fns, errs, Γ ⦄
        con ⊢ let e : τ := call f with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_apply (args : E.args tags_t) (x : string)
              (i : tags_t) (params : E.params)
              (tbls : tblenv) (aa : aenv) (cis : cienv) (eis : eienv) :
      cis x = Some params ->
      F.relfs
        (P.rel_paramarg
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
        args params ->
      ⦃ fns, errs, Γ ⦄ ApplyBlock tbls aa cis eis ⊢ apply x with args @ i ⊣ ⦃ Γ, C ⦄
  | chk_invoke (tbl : string) (i : tags_t) (tbls : tblenv)
               (aa : aenv) (cis : cienv) (eis : eienv) :
      tbls tbl = Some tt ->
      ⦃ fns, errs, Γ ⦄ ApplyBlock tbls aa cis eis ⊢ invoke tbl @ i ⊣ ⦃ Γ, C ⦄
  | chk_extern_call_void (e : string) (f : string)
                         (args : E.args tags_t) (i : tags_t) (con : ctx)
                         (eis : eienv) (params : E.params)
                         (mhds : F.fs string E.arrowT) :
      eis e = Some mhds ->
      F.get f mhds = Some (P.Arrow params None) ->
      extern_call_ok eis con ->
      F.relfs
        (P.rel_paramarg
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
        args params ->
      ⦃ fns, errs, Γ ⦄
        con ⊢ extern e calls f with args gives None @ i ⊣ ⦃ Γ, C ⦄
  | chk_extern_call_fruit (extrn : string) (f : string)
                          (args : E.args tags_t) (e : E.e tags_t)
                          (i : tags_t) (con : ctx) (eis : eienv)
                          (params: E.params) (τ : E.t)
                          (mhds : F.fs string E.arrowT) :
      eis extrn = Some mhds ->
      F.get f mhds = Some (P.Arrow params (Some τ)) ->
      extern_call_ok eis con ->
      F.relfs
        (P.rel_paramarg
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
           (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
        args params ->
      let result := Some (τ,e) in
      (⦃ fns, errs, Γ ⦄
        con ⊢ extern extrn calls f with args gives result @ i ⊣ ⦃ Γ, C ⦄)
  where "⦃ fe , ers , g1 ⦄ con ⊢ s ⊣ ⦃ g2 , sg ⦄" := (check_stmt fe ers g1 con s g2 sg).
  (**[]*)

  (** Parser State typing. *)
  Inductive check_parser_state
            {tags_t : Type} (fns : fenv) (pis : pienv) (eis : eienv)
            (sts : user_states) (errs : errors) (Γ : gamma)
    : PR.state_block tags_t -> Prop :=
  | chk_state (s : ST.s tags_t) (e : PR.e tags_t)
              (Γ' : gamma) (sg : signal) :
      ⦃ fns, errs, Γ ⦄ Parser pis eis ⊢ s ⊣ ⦃ Γ' , sg ⦄ ->
      ⟅ sts, errs, Γ' ⟆ ⊢ e ->
      ⟅⟅ fns, pis, eis, sts, errs, Γ ⟆⟆ ⊢ state { s } transition e
  where "'⟅⟅' fns , pis , eis , sts , errs , Γ '⟆⟆' ⊢ s"
          := (check_parser_state fns pis eis sts errs Γ s).
  (**[]*)

  (** Control declaration typing. *)
  Inductive check_ctrldecl
            {tags_t : Type} (tbls : tblenv) (acts : aenv) (cs : cenv) (fns : fenv)
            (cis : cienv) (eis : eienv)
            (errs : errors) (Γ : gamma)
    : CD.d tags_t -> aenv -> tblenv -> Prop :=
  | chk_action (a : string)
               (signature : E.params)
               (body : ST.s tags_t) (i : tags_t)
               (Γ' Γ'' : gamma) (sg : signal) :
      bind_all signature Γ = Γ' ->
      ⦃ fns, errs, Γ' ⦄ Action acts eis ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      ⦅ tbls, acts, cs, fns, cis, eis, errs, Γ ⦆
        ⊢ action a ( signature ) { body } @ i
        ⊣ ⦅ a ↦ signature ;; acts, tbls ⦆
  | chk_table (t : string)
              (kys : list (E.t * E.e tags_t * E.matchkind))
              (actns : list string) (i : tags_t) :
      (* Keys type. *)
      Forall (fun '(τ,e,_) => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) kys ->
      (* Actions available *)
      Forall (fun a => exists pms, acts a = Some pms) actns ->
      ⦅ tbls, acts, cs, fns, cis, eis, errs, Γ ⦆
        ⊢ table t key:=kys actions:=actns @ i ⊣ ⦅ acts, t ↦ tt;; tbls ⦆
  | chk_ctrldecl_seq (d1 d2 : CD.d tags_t) (i : tags_t)
                     (acts' acts'' : aenv) (tbls' tbls'' : tblenv) :
      ⦅ tbls, acts, cs, fns, cis, eis, errs, Γ ⦆
        ⊢ d1 ⊣ ⦅ acts', tbls'  ⦆ ->
      ⦅ tbls', acts', cs, fns, cis, eis, errs, Γ ⦆
        ⊢ d2 ⊣ ⦅ acts'', tbls'' ⦆ ->
      ⦅ tbls, acts, cs, fns, cis, eis, errs, Γ  ⦆
        ⊢ d1 ;c; d2 @ i ⊣ ⦅ acts'', tbls'' ⦆
  where
  "⦅ ts1 , as1 , cs , fs , ci1 , ei1 , errs , g1 ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
    := (check_ctrldecl ts1 as1 cs fs ci1 ei1 errs g1 d as2 ts2).
  (**[]*)

  (** Top-level declaration typing. *)
  Inductive check_topdecl
            {tags_t : Type} (cs : cenv) (fns : fenv)
            (cis : cienv) (pis : pienv) (eis : eienv)
            (errs : errors) (Γ : gamma)
            : TD.d tags_t -> eienv -> pienv -> cienv -> fenv -> cenv -> Prop :=
  | chk_instantiate_control (c : string) (x : string)
                            (cparams : E.constructor_params)
                            (cargs : E.constructor_args tags_t)
                            (i : tags_t) (params : E.params) :
      cs c = Some {{{ ControlType cparams params }}} ->
      F.relfs
        (fun carg cparam =>
           match carg, cparam with
           | E.CAExpr e, E.CTType τ
             => ⟦ errs , Γ ⟧ ⊢ e ∈ τ
           | E.CAName ctrl, {{{ ControlType cps ps }}}
             => cs ctrl = Some {{{ ControlType cps ps }}}
           | E.CAName extrn, {{{ Extern cps { mthds } }}}
             => cs extrn = Some {{{ Extern cps { mthds } }}}
           | _, _ => False
           end) cargs cparams ->
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ Instance x of c(cargs) @ i ⊣ ⦗ eis, pis, x ↦ params ;; cis, fns, cs ⦘
  | chk_instantiate_parser (p : string) (x : string)
                           (cparams : E.constructor_params)
                           (cargs : E.constructor_args tags_t)
                           (i : tags_t) (params : E.params) :
      cs p = Some {{{ ParserType cparams params }}} ->
      F.relfs
        (fun carg cparam =>
           match carg, cparam with
           | E.CAExpr e, E.CTType τ
             => ⟦ errs , Γ ⟧ ⊢ e ∈ τ
           | E.CAName prsr, {{{ ParserType cps ps }}}
             => cs prsr = Some {{{ ParserType cps ps }}}
           | E.CAName extrn, {{{ Extern cps { mthds } }}}
             => cs extrn = Some {{{ Extern cps { mthds } }}}
           | _, _ => False
           end) cargs cparams ->
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ Instance x of p(cargs) @ i ⊣ ⦗ eis, x ↦ params ;; pis, cis, fns, cs ⦘
  | chk_instantiate_extern (e : string) (x : string)
                           (cparams : E.constructor_params)
                           (cargs : E.constructor_args tags_t) (i : tags_t)
                           (mthds : F.fs string E.arrowT) :
      cs e = Some {{{ Extern cparams { mthds } }}} ->
      F.relfs
        (fun carg cparam =>
           match carg, cparam with
           | E.CAExpr e, E.CTType τ
             => ⟦ errs , Γ ⟧ ⊢ e ∈ τ
           | E.CAName extrn, {{{ Extern cps { mthds } }}}
             => cs extrn = Some {{{ Extern cps { mthds } }}}
           | _, _ => False
           end) cargs cparams ->
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ Instance x of e(cargs) @ i ⊣ ⦗ x ↦ mthds ;; eis, pis, cis, fns, cs ⦘
  | chk_control (c : string) (cparams : E.constructor_params)
                (params : E.params) (body : CD.d tags_t)
                (apply_blk : ST.s tags_t) (i : tags_t)
                (Γ' Γ'' Γ''' : gamma) (sg : signal)
                (cis' : cienv) (eis' : eienv)
                (tbls : tblenv) (acts : aenv) :
      cbind_all cparams (Γ,cis,pis,eis) = (Γ',cis',pis,eis') ->
      (* Control declarations. *)
      ⦅ ∅, ∅, cs, fns, cis', eis', errs, Γ' ⦆
        ⊢ body ⊣ ⦅ acts, tbls ⦆ ->
      bind_all params Γ' = Γ'' ->
      (* Apply block. *)
      ⦃ fns, errs, Γ'' ⦄
        ApplyBlock tbls acts cis eis ⊢ apply_blk ⊣ ⦃ Γ''', sg ⦄ ->
      let ctor := E.CTControl cparams params in
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ control c (cparams)(params) apply { apply_blk } where { body } @ i
        ⊣ ⦗ eis, pis, cis, fns, c ↦ ctor;; cs ⦘
  | chk_parser (p : string)
               (cparams : E.constructor_params)
               (params : E.params) (start_state : PR.state_block tags_t)
               (states : F.fs string (PR.state_block tags_t)) (i : tags_t)
               (pis' : pienv) (eis' : eienv)
               (Γ' Γ'' : gamma) :
      let sts := F.fold
                   (fun st _ acc => !{ st ↦ tt;; acc }!) states !{ ∅ }! in
      cbind_all cparams (Γ,cis,pis,eis) = (Γ',cis,pis',eis') ->
      bind_all params Γ' = Γ'' ->
      ⟅⟅ fns, pis', eis', sts, errs, Γ'' ⟆⟆ ⊢ start_state ->
      F.predfs_data
        (fun pst => ⟅⟅ fns, pis', eis', sts, errs, Γ'' ⟆⟆ ⊢ pst)
        states ->
      let prsr := E.CTParser cparams params in
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ parser p (cparams)(params) start:= start_state { states } @ i
        ⊣ ⦗ eis, pis, cis, fns, p ↦ prsr;; cs ⦘
  | chk_extern (e : string)
               (cparams : E.constructor_params)
               (mthds : F.fs string E.arrowT) (i : tags_t) :
      let extrn := {{{ Extern cparams { mthds } }}} in
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ extern e (cparams) { mthds } @ i
        ⊣ ⦗ eis, pis, cis, fns, e ↦ extrn;; cs ⦘
  | chk_fruit_function (f : string) (params : E.params)
                       (τ : E.t) (body : ST.s tags_t) (i : tags_t)
                       (Γ' Γ'' : gamma) (sg : signal) :
      bind_all params Γ = Γ' ->
      ⦃ fns, errs, Γ' ⦄ Function τ ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      let func := P.Arrow params (Some τ) in
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ fn f (params) -> τ { body } @ i ⊣ ⦗ eis, pis, cis, f ↦ func;;  fns, cs ⦘
  | chk_void_function (f : string) (params : E.params)
                      (body : ST.s tags_t) (i : tags_t)
                      (Γ' Γ'' : gamma) (sg : signal) :
      bind_all params Γ = Γ' ->
      ⦃ fns, errs, Γ' ⦄ Void ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
      let func := P.Arrow params None in
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘
        ⊢ void f (params) { body } @ i ⊣ ⦗ eis, pis, cis, f ↦ func;;  fns, cs ⦘
  | chk_topdecl_seq (d1 d2 : TD.d tags_t) (i : tags_t)
                    (eis' eis'' : eienv)
                    (pis' pis'' : pienv) (cis' cis'' : cienv)
                    (fns' fns'' : fenv) (cs' cs'' : cenv) :
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘ ⊢ d1
                                        ⊣ ⦗ eis', pis', cis', fns', cs' ⦘ ->
      ⦗ cs', fns', cis', pis', eis', errs, Γ⦘ ⊢ d2
                                          ⊣ ⦗ eis'', pis'', cis'', fns'', cs'' ⦘ ->
      ⦗ cs, fns, cis, pis, eis, errs, Γ ⦘ ⊢ d1 ;%; d2 @ i
                                  ⊣ ⦗ eis'', pis'', cis'', fns'', cs'' ⦘
  where
  "⦗ cs1 , fs1 , ci1 , pi1 , ei1 , ers , g1 ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , fs2 , cs2 ⦘"
    := (check_topdecl cs1 fs1 ci1 pi1 ei1 ers g1 d ei2 pi2 ci2 fs2 cs2).
  (**[]*)
End Typecheck.
