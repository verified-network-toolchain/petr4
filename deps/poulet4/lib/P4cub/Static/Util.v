Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Export Poulet4.P4Arith Poulet4.P4cub.Envn Poulet4.P4cub.Syntax.Syntax.

(** Notation entries. *)
Declare Custom Entry p4signal.
Declare Custom Entry p4context.

Module P := P4cub.
Module E := P.Expr.
Module PT := ProperType.
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
    Env.find x errs = Some tt ->
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
| pc_tuple_struct (ts : list E.t) (fs : F.fs string E.t) :
    ts = F.values fs ->
    proper_cast {{ tuple ts }} {{ struct { fs } }}
| pc_tuple_hdr (ts : list E.t) (fs : F.fs string E.t) :
    ts = F.values fs ->
    Forall PT.proper_inside_header ts ->
    proper_cast {{ tuple ts }} {{ hdr { fs } }}.
(**[]*)

(** Evidence member operations are valid on a type. *)
Inductive member_type : F.fs string E.t -> E.t -> Prop :=
| mt_struct ts : member_type ts {{ struct { ts } }}
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

(** Available constructor signatures. *)
Definition cenv : Type := Env.t string E.ct.

(** Available Package Instances. *)
Definition pkgienv : Type := strs.

(** Available Extern Constructors. *)
Definition extenv : Type :=
  Env.t string (E.constructor_params * F.fs string E.arrowT).
(**[]*)

(** Put parameters into environment. *)
Definition bind_all : E.params -> gamma -> gamma :=
  F.fold (fun x '(P.PAIn τ | P.PAOut τ | P.PAInOut τ) Γ => !{ x ↦ τ ;; Γ }!).
(**[]*)

(** Put (constructor) parameters into environments. *)
Definition cbind_all :
  E.constructor_params  ->
  gamma * pkgienv * cienv * pienv * eienv ->
  gamma * pkgienv * cienv * pienv * eienv :=
  F.fold (fun x c '(Γ, pkgis, cis, pis, eis) =>
            match c with
            | {{{ VType τ }}}
              => (!{ x ↦ τ;; Γ }!, pkgis, cis, pis, eis)
            | {{{ ControlType _ pars }}}
              => (Γ, pkgis, !{ x ↦ pars;; cis }!, pis, eis)
            | {{{ ParserType _  pars }}}
              => (Γ, pkgis, cis, !{ x ↦ pars;; pis }!, eis)
            | {{{ Extern _  { mhds } }}}
              => (Γ, pkgis, cis, pis, !{ x ↦ mhds;; eis }!)
            | {{{ PackageType _ }}}
              => (Γ, !{ x ↦ tt;; pkgis }!, cis, pis, eis)
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
    Env.find st us = Some tt ->
    valid_state us ={ δ st }=.
(**[]*)

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
