Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.AST Poulet4.P4Arith
        Poulet4.P4cub.Envn Poulet4.P4cub.Static.Util.

(** Expression typing. *)
Reserved Notation "⟦ ers , gm ⟧ ⊢ e ∈ t"
         (at level 40, e custom p4expr, t custom p4type,
          gm custom p4env, ers custom p4env).

(** Statement typing. *)
Reserved Notation "⦃ fns , errs , g1 ⦄ ctx ⊢ s ⊣ ⦃ g2 , sg ⦄"
         (at level 40, s custom p4stmt, ctx custom p4context,
          g2 custom p4env, sg custom p4signal,
          g1 custom p4env, fns custom p4env, errs custom p4env).

(** Parser-expression typing. *)
Reserved Notation "⟅ sts , ers , gm ⟆ ⊢ e"
         (at level 40, e custom p4prsrexpr,
          sts custom p4env, ers custom p4env, gm custom p4env).

(** Parser-state-block typing. *)
Reserved Notation "'⟅⟅' fns , pis , eis , sts , errs , Γ '⟆⟆' ⊢ s"
         (at level 40, s custom p4prsrstateblock,
          fns custom p4env, pis custom p4env,
          eis custom p4env, sts custom p4env,
          errs custom p4env, Γ custom p4env).

(** Control-declaration typing. *)
Reserved Notation
         "⦅ ts1 , as1 , fs , ci , ei , errs , g ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
         (at level 60, d custom p4ctrldecl,
          ts1 custom p4env, as1 custom p4env,
          ts2 custom p4env, as2 custom p4env,
          fs custom p4env, ci custom p4env,
          ei custom p4env, errs custom p4env,
          g custom p4env).

(** Toplevel-declaration typing. *)
Reserved Notation
         "⦗ cs1 , fs1 , pgi1 , ci1 , pi1 , ei1 , ers ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , pgi2 , fs2 , cs2 ⦘"
         (at level 70, d custom p4topdecl, ers custom p4env,
          ei1 custom p4env, pi1 custom p4env,
          ei2 custom p4env, pi2 custom p4env,
          ci1 custom p4env, fs1 custom p4env,
          ci2 custom p4env, fs2 custom p4env,
          cs1 custom p4env, pgi1 custom p4env,
          cs2 custom p4env, pgi2 custom p4env).

Module P := P4cub.
Module E := P.Expr.
Module PT := ProperType.
Module ST := P.Stmt.
Module PR := P.Parser.
Module CD := P.Control.ControlDecl.
Module TD := P.TopDecl.
Module F := P.F.
Import P.P4cubNotations.
Import Env.EnvNotations.

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
    Env.find x Γ = Some τ ->
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
| chk_struct_lit (efs : F.fs string (E.t * E.e tags_t))
                 (tfs : F.fs string E.t) (i : tags_t) :
    F.relfs
      (fun te τ =>
         (fst te) = τ /\
         let e := snd te in
         ⟦ errs , Γ ⟧ ⊢ e ∈ τ) efs tfs ->
    ⟦ errs , Γ ⟧ ⊢ struct { efs } @ i ∈ struct { tfs }
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
    Env.find f fns = Some (P.Arrow params None) ->
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
    Env.find a aa = Some params ->
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
    Env.find f fns = Some (P.Arrow params (Some τ)) ->
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
    Env.find x cis = Some params ->
    F.relfs
      (P.rel_paramarg
         (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
         (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
      args params ->
    ⦃ fns, errs, Γ ⦄ ApplyBlock tbls aa cis eis
                     ⊢ apply x with args @ i ⊣ ⦃ Γ, C ⦄
| chk_invoke (tbl : string) (i : tags_t) (tbls : tblenv)
             (aa : aenv) (cis : cienv) (eis : eienv) :
    Env.find tbl tbls = Some tt ->
    ⦃ fns, errs, Γ ⦄ ApplyBlock tbls aa cis eis ⊢ invoke tbl @ i ⊣ ⦃ Γ, C ⦄
| chk_extern_call_void (e : string) (f : string)
                       (args : E.args tags_t) (i : tags_t) (con : ctx)
                       (eis : eienv) (params : E.params)
                       (mhds : F.fs string E.arrowT) :
    Env.find e eis = Some mhds ->
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
    (Env.find extrn eis = Some mhds ->
     F.get f mhds = Some (P.Arrow params (Some τ)) ->
     extern_call_ok eis con ->
     F.relfs
       (P.rel_paramarg
          (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ)
          (fun '(t,e) τ => τ = t /\ ⟦ errs, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
       args params ->
     let result := Some (τ,e) in
     (⦃ fns, errs, Γ ⦄
       con ⊢ extern extrn calls f with args gives result @ i ⊣ ⦃ Γ, C ⦄))
where "⦃ fe , ers , g1 ⦄ con ⊢ s ⊣ ⦃ g2 , sg ⦄"
        := (check_stmt fe ers g1 con s g2 sg).
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
Inductive check_ctrldecl {tags_t : Type}
          (tbls : tblenv) (acts : aenv) (fns : fenv)
          (cis : cienv) (eis : eienv)
          (errs : errors) (Γ : gamma)
  : CD.d tags_t -> aenv -> tblenv -> Prop :=
| chk_action (a : string)
             (signature : E.params)
             (body : ST.s tags_t) (i : tags_t)
             (Γ' Γ'' : gamma) (sg : signal) :
    bind_all signature Γ = Γ' ->
    ⦃ fns, errs, Γ' ⦄ Action acts eis ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    ⦅ tbls, acts, fns, cis, eis, errs, Γ ⦆
      ⊢ action a ( signature ) { body } @ i
      ⊣ ⦅ a ↦ signature ;; acts, tbls ⦆
| chk_table (t : string)
            (kys : list (E.t * E.e tags_t * E.matchkind))
            (actns : list string) (i : tags_t) :
    (* Keys type. *)
    Forall (fun '(τ,e,_) => ⟦ errs, Γ ⟧ ⊢ e ∈ τ) kys ->
    (* Actions available *)
    Forall (fun a => exists pms, Env.find a acts = Some pms) actns ->
    ⦅ tbls, acts, fns, cis, eis, errs, Γ ⦆
      ⊢ table t key:=kys actions:=actns @ i ⊣ ⦅ acts, t ↦ tt;; tbls ⦆
| chk_ctrldecl_seq (d1 d2 : CD.d tags_t) (i : tags_t)
                   (acts' acts'' : aenv) (tbls' tbls'' : tblenv) :
    ⦅ tbls, acts, fns, cis, eis, errs, Γ ⦆
      ⊢ d1 ⊣ ⦅ acts', tbls'  ⦆ ->
    ⦅ tbls', acts', fns, cis, eis, errs, Γ ⦆
      ⊢ d2 ⊣ ⦅ acts'', tbls'' ⦆ ->
    ⦅ tbls, acts, fns, cis, eis, errs, Γ  ⦆
      ⊢ d1 ;c; d2 @ i ⊣ ⦅ acts'', tbls'' ⦆
where
"⦅ ts1 , as1 , fs , ci1 , ei1 , errs , g1 ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
  := (check_ctrldecl ts1 as1 fs ci1 ei1 errs g1 d as2 ts2).
(**[]*)

(** Top-level declaration typing. *)
Inductive check_topdecl
          {tags_t : Type} (cs : cenv) (fns : fenv)
          (pgis : pkgienv) (cis : cienv) (pis : pienv) (eis : eienv)
          (errs : errors)
  : TD.d tags_t -> eienv -> pienv -> cienv -> pkgienv -> fenv -> cenv -> Prop :=
| chk_instantiate_control (c x : string)
                          (cparams : E.constructor_params)
                          (cargs : E.constructor_args tags_t)
                          (i : tags_t) (params : E.params) :
    Env.find c cs = Some {{{ ControlType cparams params }}} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | E.CAExpr e, {{{ VType τ }}}
           => ⟦ errs , ∅ ⟧ ⊢ e ∈ τ
         | E.CAName ctrl, {{{ ControlType cps ps }}}
           => Env.find ctrl cs = Some {{{ ControlType cps ps }}}
         | E.CAName extrn, {{{ Extern cps { mthds } }}}
           => Env.find extrn cs = Some {{{ Extern cps { mthds } }}}
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis, errs⦘
      ⊢ Instance x of c(cargs) @ i
      ⊣ ⦗ eis, pis, x ↦ params ;; cis, pgis, fns, cs ⦘
| chk_instantiate_parser (p x : string)
                         (cparams : E.constructor_params)
                         (cargs : E.constructor_args tags_t)
                         (i : tags_t) (params : E.params) :
    Env.find p cs = Some {{{ ParserType cparams params }}} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | E.CAExpr e, {{{ VType τ }}}
           => ⟦ errs , ∅ ⟧ ⊢ e ∈ τ
         | E.CAName prsr, {{{ ParserType cps ps }}}
           => Env.find prsr cs = Some {{{ ParserType cps ps }}}
         | E.CAName extrn, {{{ Extern cps { mthds } }}}
           => Env.find extrn cs = Some {{{ Extern cps { mthds } }}}
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ Instance x of p(cargs) @ i
      ⊣ ⦗ eis, x ↦ params ;; pis, cis, pgis, fns, cs ⦘
| chk_instantiate_extern (e x : string)
                         (cparams : E.constructor_params)
                         (cargs : E.constructor_args tags_t) (i : tags_t)
                         (mthds : F.fs string E.arrowT) :
    Env.find e cs = Some {{{ Extern cparams { mthds } }}} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | E.CAExpr e, {{{ VType τ }}}
           => ⟦ errs , ∅ ⟧ ⊢ e ∈ τ
         | E.CAName extrn, {{{ Extern cps { mthds } }}}
           => Env.find extrn cs = Some {{{ Extern cps { mthds } }}}
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ Instance x of e(cargs) @ i ⊣ ⦗ x ↦ mthds ;; eis, pis, cis, pgis, fns, cs ⦘
| chk_instantiate_package (pkg x : string)
                          (cparams : E.constructor_params)
                          (cargs : E.constructor_args tags_t)
                          (i : tags_t) :
    Env.find pkg cs = Some {{{ PackageType cparams }}} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | E.CAExpr e, {{{ VType τ }}}
           => ⟦ errs , ∅ ⟧ ⊢ e ∈ τ
         | E.CAName ctrl, {{{ ControlType cps ps }}}
           => Env.find ctrl cs = Some {{{ ControlType cps ps }}}
         | E.CAName prsr, {{{ ParserType cps ps }}}
           => Env.find prsr cs = Some {{{ ParserType cps ps }}}
         | E.CAName extrn, {{{ Extern cps { mthds } }}}
           => Env.find extrn cs = Some {{{ Extern cps { mthds } }}}
         | _, _ => False
         end)
      cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ Instance x of pkg(cargs) @ i ⊣ ⦗ eis, pis, cis, x ↦ tt ;; pgis, fns, cs ⦘
| chk_control (c : string) (cparams : E.constructor_params)
              (params : E.params) (body : CD.d tags_t)
              (apply_blk : ST.s tags_t) (i : tags_t)
              (Γ' Γ'' Γ''' : gamma) (sg : signal)
              (cis' : cienv) (eis' : eienv)
              (tbls : tblenv) (acts : aenv) :
    cbind_all cparams (!{∅}!,pgis,cis,pis,eis) = (Γ',pgis,cis',pis,eis') ->
    (* Control declarations. *)
    ⦅ ∅, ∅, fns, cis', eis', errs, Γ' ⦆
      ⊢ body ⊣ ⦅ acts, tbls ⦆ ->
    bind_all params Γ' = Γ'' ->
    (* Apply block. *)
    ⦃ fns, errs, Γ'' ⦄
      ApplyBlock tbls acts cis eis ⊢ apply_blk ⊣ ⦃ Γ''', sg ⦄ ->
    let ctor := E.CTControl cparams params in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ control c (cparams)(params) apply { apply_blk } where { body } @ i
        ⊣ ⦗ eis, pis, cis, pgis, fns, c ↦ ctor;; cs ⦘
| chk_parser (p : string)
             (cparams : E.constructor_params)
             (params : E.params) (start_state : PR.state_block tags_t)
             (states : F.fs string (PR.state_block tags_t)) (i : tags_t)
             (pis' : pienv) (eis' : eienv)
             (Γ' Γ'' : gamma) :
    let sts := F.fold
                 (fun st _ acc => !{ st ↦ tt;; acc }!) states !{ ∅ }! in
    cbind_all cparams (!{∅}!,pgis,cis,pis,eis) = (Γ',pgis,cis,pis',eis') ->
    bind_all params Γ' = Γ'' ->
    ⟅⟅ fns, pis', eis', sts, errs, Γ'' ⟆⟆ ⊢ start_state ->
    F.predfs_data
      (fun pst => ⟅⟅ fns, pis', eis', sts, errs, Γ'' ⟆⟆ ⊢ pst) states ->
    let prsr := E.CTParser cparams params in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ parser p (cparams)(params) start:= start_state { states } @ i
      ⊣ ⦗ eis, pis, cis, pgis, fns, p ↦ prsr;; cs ⦘
| chk_extern (e : string)
             (cparams : E.constructor_params)
             (mthds : F.fs string E.arrowT) (i : tags_t) :
    let extrn := {{{ Extern cparams { mthds } }}} in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ extern e (cparams) { mthds } @ i
      ⊣ ⦗ eis, pis, cis, pgis, fns, e ↦ extrn;; cs ⦘
| chk_package (pkg : string) (cparams : E.constructor_params) (i : tags_t) :
    let pkge := {{{ PackageType cparams }}} in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ package pkg (cparams) @ i
      ⊣ ⦗ eis, pis, cis, pgis, fns, pkg ↦ pkge;; cs ⦘
| chk_fruit_function (f : string) (params : E.params)
                     (τ : E.t) (body : ST.s tags_t) (i : tags_t)
                     (Γ' Γ'' : gamma) (sg : signal) :
    bind_all params !{∅}! = Γ' ->
    ⦃ fns, errs, Γ' ⦄ Function τ ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    let func := P.Arrow params (Some τ) in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ fn f (params) -> τ { body } @ i
      ⊣ ⦗ eis, pis, cis, pgis, f ↦ func;;  fns, cs ⦘
| chk_void_function (f : string) (params : E.params)
                    (body : ST.s tags_t) (i : tags_t)
                    (Γ' Γ'' : gamma) (sg : signal) :
    bind_all params !{∅}! = Γ' ->
    ⦃ fns, errs, Γ' ⦄ Void ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    let func := P.Arrow params None in
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘
      ⊢ void f (params) { body } @ i
      ⊣ ⦗ eis, pis, cis, pgis, f ↦ func;;  fns, cs ⦘
| chk_topdecl_seq (d1 d2 : TD.d tags_t) (i : tags_t)
                  (eis' eis'' : eienv) (pgis' pgis'' : pkgienv)
                  (pis' pis'' : pienv) (cis' cis'' : cienv)
                  (fns' fns'' : fenv) (cs' cs'' : cenv) :
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘ ⊢ d1
    ⊣ ⦗ eis', pis', cis', pgis', fns', cs' ⦘ ->
    ⦗ cs', fns', pgis', cis', pis', eis', errs ⦘ ⊢ d2
    ⊣ ⦗ eis'', pis'', cis'', pgis'', fns'', cs'' ⦘ ->
    ⦗ cs, fns, pgis, cis, pis, eis, errs ⦘ ⊢ d1 ;%; d2 @ i
    ⊣ ⦗ eis'', pis'', cis'', pgis'', fns'', cs'' ⦘
where
"⦗ cs1 , fs1 , pgi1 , ci1 , pi1 , ei1 , ers ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , pgi2 , fs2 , cs2 ⦘"
  := (check_topdecl cs1 fs1 pgi1 ci1 pi1 ei1 ers d ei2 pi2 ci2 pgi2 fs2 cs2).
(**[]*)
