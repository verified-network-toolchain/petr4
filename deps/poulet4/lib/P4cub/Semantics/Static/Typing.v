Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util.
Import String.

Import AllCubNotations Clmt.Notations.

(** * Expression typing. *)

Record expr_type_env : Set := { type_vars:nat; types:list Expr.t }.

Reserved Notation "Γ '⊢ₑ' e ∈ t" (at level 80, no associativity).

Local Open Scope ty_scope.
Local Open Scope expr_scope.

Inductive type_expr (Γ : expr_type_env)
  : Expr.e -> Expr.t -> Prop :=
| type_bool (b : bool) :
  Γ ⊢ₑ b ∈ Expr.TBool
| type_bit w n :
  BitArith.bound w n ->
  Γ ⊢ₑ w `W n ∈ Expr.TBit w
| type_int w n :
  IntArith.bound w n ->
  Γ ⊢ₑ (Npos w) `S n ∈ Expr.TInt (Npos w)
| type_var x τ :
  nth_error (types Γ) x = Some τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ Expr.Var τ x ∈ τ
| type_slice e hi lo w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  Γ ⊢ₑ e ∈ τ ->
  Γ ⊢ₑ Expr.Slice e hi lo ∈ Expr.TBit (Npos (hi - lo + 1)%positive)
| type_cast τ τ' e :
    proper_cast τ' τ ->
    t_ok (type_vars Γ) τ' ->
    t_ok (type_vars Γ) τ ->
    Γ ⊢ₑ e ∈ τ' ->
    Γ ⊢ₑ Expr.Cast τ e ∈ τ
| type_uop op τ τ' e :
    uop_type op τ τ' ->
    Γ ⊢ₑ e ∈ τ ->
    Γ ⊢ₑ Expr.Uop τ' op e ∈ τ'
| type_bop op τ1 τ2 τ e1 e2 :
    bop_type op τ1 τ2 τ ->
    Γ ⊢ₑ e1 ∈ τ1 ->
    Γ ⊢ₑ e2 ∈ τ2 ->
    Γ ⊢ₑ Expr.Bop τ op e1 e2 ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e ∈ Expr.TStruct τs b ->
  Γ ⊢ₑ Expr.Member τ x e ∈ τ
| type_struct es oe τs (b : bool) :
  relop (type_expr Γ) oe (if b then Some Expr.TBool else None) ->
  Forall2 (type_expr Γ) es τs ->
  Γ ⊢ₑ Expr.Struct es oe ∈ Expr.TStruct τs b
| type_error err :
  Γ ⊢ₑ Expr.Error err ∈ Expr.TError
where "gm '⊢ₑ' e ∈ ty" := (type_expr gm e ty) : type_scope.

Local Close Scope expr_scope.
Local Open Scope pat_scope.

(** Select-pattern-typing. *)
Inductive type_pat : Parser.pat -> Expr.t -> Prop :=
| type_wild t : type_pat Parser.Wild t
| type_mask p1 p2 w :
  type_pat p1 (Expr.TBit w) ->
  type_pat p2 (Expr.TBit w) ->
  type_pat (Parser.Mask p1 p2) (Expr.TBit w)
| type_range p1 p2 w :
  type_pat p1 (Expr.TBit w) ->
  type_pat p2 (Expr.TBit w) ->
  type_pat (Parser.Range p1 p2) (Expr.TBit w)
| type_pbit w n :
  type_pat (w PW n) (Expr.TBit w)
| type_pint w z :
  type_pat (w PS z) (Expr.TInt w)
| type_ptup ps ts :
  Forall2 type_pat ps ts ->
  type_pat (Parser.Struct ps) (Expr.TStruct ts false).
Local Close Scope pat_scope.

(** Parser-expression typing. *)
Inductive type_prsrexpr 
          (total_states : nat) (Γ : expr_type_env)
  : Parser.e -> Prop :=
| type_goto (st : Parser.state) :
  valid_state total_states st ->
  type_prsrexpr total_states Γ (Parser.Goto st)
| type_select e default cases τ :
  Γ ⊢ₑ e ∈ τ ->
  type_prsrexpr total_states Γ default ->
  Forall
    (fun pe =>
       let p := fst pe in
       let e := snd pe in
       type_pat p τ /\ type_prsrexpr total_states Γ e) cases ->
  type_prsrexpr total_states Γ (Parser.Select e default cases).

(** * Statement typing. *)

Record stmt_type_env : Set :=
  { functs := fenv
  ; cntx := ctx
  ; expr_env :> expr_type_env }.

Reserved Notation "Γ₁ ⊢ₛ s ⊣ Γ₂ ↓ sig" (at level 80, no associativity).

Local Open Scope stmt_scope.

Inductive type_stmt
  : stmt_type_env -> Stmt.s -> expr_type_env -> signal -> Prop :=
| type_skip Γ :
  Γ ⊢ₛ Stmt.Skip ⊣ Γ ↓ Cont
| type_seq_cont s1 s2 Δ Γ Γ' Γ'' sig con fns :
  {|functs:=fns;cntx:=con;type_vars:=Δ;types:=Γ|} ⊢ₛ s1 ⊣ Γ' ↓ Cont ->
  {|functs:=fns;cntx:=con;type_vars:=Δ;types:=Γ'|} ⊢ₛ s2 ⊣ Γ'' ↓ sig ->
  {|functs:=fns;cntx:=con;type_vars:=Δ;types:=Γ|} ⊢ₛ s1 `; s2 ⊣ Γ'' ↓ sig
| type_block s Γ Γ' sig :
  Γ ⊢ₛ s ⊣ Γ' ↓ sig ->
  Γ ⊢ₛ Stmt.Block s ⊣ Γ ↓ Cont
| type_vardecl τ eo :
    match eo with
    | inr e => Γ ⊢ₑ e ∈ τ
    | inl τ => t_ok Δ τ
    end ->
    Γ ⊢ₛ Stmt.Var eo ⊣ {| functs   := functs Γ
                       ; cntx      := cntx Γ
                       ; type_vars := type_vars Γ'
                       ; types     := τ :: types Γ|} ↓ Cont
| type_assign (τ : Expr.t) (e1 e2 : Expr.e)  (con : ctx) :
    lvalue_ok e1 ->
    ⟦ Δ, Γ ⟧ ⊢ e1 ∈ τ ->
    ⟦ Δ, Γ ⟧ ⊢ e2 ∈ τ ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ asgn e1 := e2 ⊣ ⦃ Γ, C ⦄
| type_cond (guard : Expr.e) (tru fls : Stmt.s)
           (Γ1 Γ2 : Gamma)  (sgt sgf sg : signal) (con : ctx) :
    lub sgt sgf = sg ->
    ⟦ Δ, Γ ⟧ ⊢ guard ∈ Bool ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ tru ⊣ ⦃ Γ1, sgt ⦄ ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ fls ⊣ ⦃ Γ2, sgf ⦄ ->
    ⦃ fns, Δ, Γ ⦄
      con ⊢ if guard then tru else fls ⊣ ⦃ Γ, sg ⦄
(* TODO: fix:
| type_return_void  (con : ctx) :
    return_void_ok con ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ returns None ⊣ ⦃ Γ, R ⦄
| type_return_fruit (τ : Expr.t) (e : Expr.e) :
    ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
    ⦃ fns, Δ, Γ ⦄ Function τ ⊢ return (Some e) ⊣ ⦃ Γ, R ⦄*)
| type_exit  (con : ctx) :
    exit_ctx_ok con ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ exit ⊣ ⦃ Γ, R ⦄
| type_void_call (params : Expr.params)
                (ts : list Expr.t)
                (args : Expr.args)
                (f : string)  (con : ctx) :
    fns f = Some {|paramargs:=params; rtrns:=None|} ->
    F.relfs
      (rel_paramarg_same
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ))
      args params ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ call f<ts>(args) ⊣ ⦃ Γ, C ⦄
| type_act_call (params : Expr.params)
               (args : Expr.args)
               (a : string) 
               (aa : aenv) (con : ctx) :
    action_call_ok aa con ->
    aa a = Some params ->
    F.relfs
      (rel_paramarg
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ)
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
      args params ->
    ⦃ fns, Δ, Γ ⦄ con ⊢ calling a with args ⊣ ⦃ Γ, C ⦄
| type_fun_call (τ : Expr.t) (e : Expr.e)
               (params : Expr.params)
               (ts : list Expr.t)
               (args : Expr.args)
               (f : string)  (con : ctx) :
    t_ok Δ τ ->
    fns f = Some {|paramargs:=params; rtrns:=Some τ|} ->
    F.relfs
      (rel_paramarg
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ)
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
      args params ->
    ⟦ Δ, Γ ⟧ ⊢ e ∈ τ ->
    ⦃ fns, Δ, Γ ⦄
      con ⊢ let e := call f<ts>(args) ⊣ ⦃ Γ, C ⦄
| type_apply (eargs : F.fs string string) (args : Expr.args) (x : string)
             (eps : F.fs string string) (params : Expr.params)
            (tbls : tblenv) (aa : aenv) (cis : cienv) (eis : eienv) :
    cis x = Some (eps,params) ->
    F.relfs
      (rel_paramarg
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ)
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
      args params ->
    ⦃ fns, Δ, Γ ⦄ ApplyBlock tbls aa cis eis
                     ⊢ apply x with eargs & args ⊣ ⦃ Γ, C ⦄
| type_invoke (tbl : string)  (tbls : tblenv)
             (aa : aenv) (cis : cienv) (eis : eienv) :
    In tbl tbls ->
    ⦃ fns, Δ, Γ ⦄ ApplyBlock tbls aa cis eis ⊢ invoke tbl ⊣ ⦃ Γ, C ⦄
| type_extern_call_void (e : string) (f : string)
                       (ts : list Expr.t)
                       (args : Expr.args)  (con : ctx)
                       (eis : eienv) (params : Expr.params)
                       (mhds : F.fs string Expr.arrowT) :
    eis e = Some mhds ->
    F.get f mhds = Some {|paramargs:=params; rtrns:=None|} ->
    extern_call_ok eis con ->
    F.relfs
      (rel_paramarg
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ)
         (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
      args params ->
    ⦃ fns, Δ, Γ ⦄
      con ⊢ extern e calls f<ts>(args) gives None ⊣ ⦃ Γ, C ⦄
| type_extern_call_fruit (extrn : string) (f : string)
                        (ts : list Expr.t)
                        (args : Expr.args) (e : Expr.e)
                         (con : ctx) (eis : eienv)
                        (params: Expr.params) (τ : Expr.t)
                        (mhds : F.fs string Expr.arrowT) :
    (eis extrn = Some mhds ->
     F.get f mhds = Some {|paramargs:=params; rtrns:=Some τ|} ->
     extern_call_ok eis con ->
     F.relfs
       (rel_paramarg
          (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ)
          (fun e τ => ⟦ Δ, Γ ⟧ ⊢ e ∈ τ /\ lvalue_ok e))
       args params ->
     let result := Some e in
     (⦃ fns, Δ, Γ ⦄
        con ⊢ extern extrn calls f<ts>(args) gives result ⊣ ⦃ Γ, C ⦄))
where "⦃ fe , ers , g1 ⦄ con ⊢ s ⊣ ⦃ g2 , sg ⦄"
        := (type_stmt fe ers g1 con s g2 sg).
(**[]*)
                     
(** Parser State typing. *)
Definition type_parser_state
          (fns : fenv) (pis : pienv) (eis : eienv)
          (sts : user_states) (Δ : Delta) (Γ : Gamma)
          '(&{state { s } transition e}& : Parser.state_block) : Prop :=
  exists (Γ' : Gamma) (sg : signal),
    ⦃ fns, Δ, Γ ⦄ Parser pis eis ⊢ s ⊣ ⦃ Γ' , sg ⦄.
(**[]*)

Notation "'⟅⟅' fns , pis , eis , sts , Δ , Γ '⟆⟆' ⊢ s"
  := (type_parser_state fns pis eis sts Δ Γ s).

(** Control-declaration typing. *)
Reserved Notation
         "⦅ ts1 , as1 , fs , ci , ei , g ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
         (at level 60, d custom p4ctrldecl).

(** Control declaration typing. *)
Inductive type_ctrldecl 
          (tbls : tblenv) (acts : aenv) (fns : fenv)
          (cis : cienv) (eis : eienv) (Γ : Gamma)
  : Control.d -> aenv -> tblenv -> Prop :=
| type_action (a : string)
             (signature : Expr.params)
             (body : Stmt.s) 
             (Γ' Γ'' : Gamma) (sg : signal) :
    bind_all signature Γ = Γ' ->
    ⦃ fns, [], Γ' ⦄ Action acts eis ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    ⦅ tbls, acts, fns, cis, eis, Γ ⦆
      ⊢ action a ( signature ) { body }
      ⊣ ⦅ a ↦ signature ,, acts, tbls ⦆
| type_table (t : string)
            (kys : list (Expr.e * Expr.mattypeind))
            (actns : list string) :
    (* Keys type. *)
    Forall (fun '(e,_) => exists τ, ⟦ [], Γ ⟧ ⊢ e ∈ τ) kys ->
    (* Actions available *)
    Forall (fun a => exists pms, acts a = Some pms) actns ->
    ⦅ tbls, acts, fns, cis, eis, Γ ⦆
      ⊢ table t key:=kys actions:=actns ⊣ ⦅ acts, (t :: tbls) ⦆
| type_ctrldecl_seq (d1 d2 : Control.d) 
                   (acts' acts'' : aenv) (tbls' tbls'' : tblenv) :
    ⦅ tbls, acts, fns, cis, eis, Γ ⦆
      ⊢ d1 ⊣ ⦅ acts', tbls'  ⦆ ->
    ⦅ tbls', acts', fns, cis, eis, Γ ⦆
      ⊢ d2 ⊣ ⦅ acts'', tbls'' ⦆ ->
    ⦅ tbls, acts, fns, cis, eis, Γ  ⦆
      ⊢ d1 ;c; d2 ⊣ ⦅ acts'', tbls'' ⦆
where
"⦅ ts1 , as1 , fs , ci1 , ei1 , g1 ⦆ ⊢ d ⊣ ⦅ as2 , ts2 ⦆"
  := (type_ctrldecl ts1 as1 fs ci1 ei1 g1 d as2 ts2).
(**[]*)

(** Toplevel-declaration typing. *)
Reserved Notation
         "⦗ cs1 , fs1 , pgi1 , ci1 , pi1 , ei1 ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , pgi2 , fs2 , cs2 ⦘"
         (at level 70, d custom p4topdecl).

(** Top-level declaration typing. *)
(* TODO: type parameters and arguments! *)
Inductive type_topdecl
          (cs : cenv) (fns : fenv)
          (pgis : pkgienv) (cis : cienv) (pis : pienv) (eis : eienv)
  : TopDecl.d -> eienv -> pienv -> cienv -> pkgienv -> fenv -> cenv -> Prop :=
| type_instantiate_control (c x : string)
                          (ts : list Expr.t)
                          (cparams : Expr.constructor_params)
                          (cargs : Expr.constructor_args) 
                          (extparams : F.fs string string) (params : Expr.params) :
    cs c = Some {(Expr.ControlType cparams extparams params)} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | Expr.CAExpr e, {(Expr.VType τ)}
           => ⟦ [] , ∅ ⟧ ⊢ e ∈ τ
         | Expr.CAName ctrl, {(Expr.ControlType cps eps ps)}
           => cs ctrl = Some {(Expr.ControlType cps eps ps)}
         (*| Expr.CAName extrn, {(Expr.Extern cps { mthds })}
           => cs extrn = Some {(Expr.Extern cps { mthds })}*)
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ Instance x of c<ts>(cargs)
      ⊣ ⦗ eis, pis, x ↦ (extparams,params) ,, cis, pgis, fns, cs ⦘
| type_instantiate_parser (p x : string)
                         (ts : list Expr.t)
                         (cparams : Expr.constructor_params)
                         (cargs : Expr.constructor_args) 
                         (extparams : F.fs string string)
                         (params : Expr.params) :
    cs p = Some {(Expr.ParserType cparams extparams params)} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | Expr.CAExpr e, {(Expr.VType τ)}
           => ⟦ [] , ∅ ⟧ ⊢ e ∈ τ
         | Expr.CAName prsr, {(Expr.ParserType cps eps ps)}
           => cs prsr = Some {(Expr.ParserType cps eps ps)}
         (*| Expr.CAName extrn, {(Expr.Extern cps { mthds })}
           => cs extrn = Some {(Expr.Extern cps { mthds })}*)
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ Instance x of p<ts>(cargs)
      ⊣ ⦗ eis, x ↦ (extparams,params) ,, pis, cis, pgis, fns, cs ⦘
(*| type_instantiate_extern (e x : string)
                         (cparams : Expr.constructor_params)
                         (cargs : Expr.constructor_args) 
                         (mthds : F.fs string Expr.arrowT) :
                         cs e = Some {(Expr.Extern cparams { mthds })} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | Expr.CAExpr e, {(Expr.VType τ)}
           => ⟦ \Delta , ∅ ⟧ ⊢ e ∈ τ
         | Expr.CAName extrn, {(Expr.Extern cps { mthds })}
           => cs extrn = Some {(Expr.Extern cps { mthds })}
         | _, _ => False
         end) cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis, \Delta ⦘
      ⊢ Instance x of e(cargs) ⊣ ⦗ x ↦ mthds ,, eis, pis, cis, pgis, fns, cs ⦘ *)
| type_instantiate_package (pkg x : string)
                          (ts : list Expr.t)
                          (cparams : Expr.constructor_params)
                          (cargs : Expr.constructor_args)
                          :
    cs pkg = Some {(Expr.PackageType cparams)} ->
    F.relfs
      (fun carg cparam =>
         match carg, cparam with
         | Expr.CAExpr e, {(Expr.VType τ)}
           => ⟦ [] , ∅ ⟧ ⊢ e ∈ τ
         | Expr.CAName ctrl, {(Expr.ControlType cps eps ps)}
           => cs ctrl = Some {(Expr.ControlType cps eps ps)}
         | Expr.CAName prsr, {(Expr.ParserType cps eps ps)}
           => cs prsr = Some {(Expr.ParserType cps eps ps)}
         (*| Expr.CAName extrn, {(Expr.Extern cps { mthds })}
           => cs extrn = Some {(Expr.Extern cps { mthds })}*)
         | _, _ => False
         end)
      cargs cparams ->
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      (* TODO: correctly update package instance env *)
      ⊢ Instance x of pkg<ts>(cargs) ⊣ ⦗ eis, pis, cis, (*x ↦ tt ,,*) pgis, fns, cs ⦘
| type_control (c : string) (cparams : Expr.constructor_params)
              (extparams : F.fs string string)
              (params : Expr.params) (body : Control.d)
              (apply_blk : Stmt.s) 
              (Γ' Γ'' Γ''' : Gamma) (sg : signal)
              (cis' : cienv) (eis' : eienv)
              (tbls : tblenv) (acts : aenv) :
    cbind_all cparams (∅,pgis,cis,pis,eis) = (Γ',pgis,cis',pis,eis') ->
    (* Control declarations. *)
    ⦅ [], ∅, fns, cis', eis', Γ' ⦆
      ⊢ body ⊣ ⦅ acts, tbls ⦆ ->
    bind_all params Γ' = Γ'' ->
    (* Apply block. *)
    ⦃ fns, [], Γ'' ⦄
      ApplyBlock tbls acts cis eis ⊢ apply_blk ⊣ ⦃ Γ''', sg ⦄ ->
    let ctor := Expr.CTControl cparams extparams params in
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ control c (cparams)(extparams)(params) apply { apply_blk } where { body }
        ⊣ ⦗ eis, pis, cis, pgis, fns, c ↦ ctor,, cs ⦘
| type_parser (p : string)
             (cparams : Expr.constructor_params)
             (extparams : F.fs string string)
             (params : Expr.params) (start_state : Parser.state_block)
             (states : F.fs string (Parser.state_block)) 
             (pis' : pienv) (eis' : eienv)
             (Γ' Γ'' : Gamma) :
    let sts := F.fold
                 (fun st _ acc => st :: acc) states [] in
    cbind_all cparams (∅,pgis,cis,pis,eis) = (Γ',pgis,cis,pis',eis') ->
    bind_all params Γ' = Γ'' ->
    ⟅⟅ fns, pis', eis', sts, [], Γ'' ⟆⟆ ⊢ start_state ->
    F.predfs_data
      (fun pst => ⟅⟅ fns, pis', eis', sts, [], Γ'' ⟆⟆ ⊢ pst) states ->
    let prsr := Expr.CTParser cparams extparams params in
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ parser p (cparams)(extparams)(params) start:= start_state { states }
      ⊣ ⦗ eis, pis, cis, pgis, fns, p ↦ prsr,, cs ⦘
(*| type_extern (e : string)
             (cparams : Expr.constructor_params)
             (mthds : F.fs string Expr.arrowT) :
    let extrn := {(Expr.Extern cparams { mthds })} in
    ⦗ cs, fns, pgis, cis, pis, eis, \Delta ⦘
      ⊢ extern e (cparams) { mthds }
      ⊣ ⦗ eis, pis, cis, pgis, fns, e ↦ extrn,, cs ⦘ *)
(*| type_package (pkg : string)
              (TS : list string)
              (cparams : Expr.constructor_params) :
    let pkge := {(Expr.PackageType cparams)} in
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ package pkg <TS> (cparams)
      ⊣ ⦗ eis, pis, cis, pgis, fns, pkg ↦ pkge,, cs ⦘*)
| type_fruit_function (f : string) (params : Expr.params)
                     (Δ : list string)
                     (τ : Expr.t) (body : Stmt.s) 
                     (Γ' Γ'' : Gamma) (sg : signal) :
    bind_all params ∅ = Γ' ->
    ⦃ fns, Δ, Γ' ⦄ Function τ ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    let func := {|paramargs:=params; rtrns:=Some τ|} in
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ fn f <Δ> (params) -> τ { body }
      ⊣ ⦗ eis, pis, cis, pgis, f ↦ func,,  fns, cs ⦘
| type_void_function (f : string) (Δ : Delta)
                    (params : Expr.params)
                    (body : Stmt.s) 
                    (Γ' Γ'' : Gamma) (sg : signal) :
    bind_all params ∅ = Γ' ->
    ⦃ fns, Δ, Γ' ⦄ Void ⊢ body ⊣ ⦃ Γ'', sg ⦄ ->
    let func := {|paramargs:=params; rtrns:=None|} in
    ⦗ cs, fns, pgis, cis, pis, eis ⦘
      ⊢ void f<Δ>(params) { body }
      ⊣ ⦗ eis, pis, cis, pgis, f ↦ func,,  fns, cs ⦘
| type_topdecl_seq (d1 d2 : TopDecl.d) 
                  (eis' eis'' : eienv) (pgis' pgis'' : pkgienv)
                  (pis' pis'' : pienv) (cis' cis'' : cienv)
                  (fns' fns'' : fenv) (cs' cs'' : cenv) :
    ⦗ cs, fns, pgis, cis, pis, eis ⦘ ⊢ d1
    ⊣ ⦗ eis', pis', cis', pgis', fns', cs' ⦘ ->
    ⦗ cs', fns', pgis', cis', pis', eis' ⦘ ⊢ d2
    ⊣ ⦗ eis'', pis'', cis'', pgis'', fns'', cs'' ⦘ ->
    ⦗ cs, fns, pgis, cis, pis, eis ⦘ ⊢ d1 ;%; d2
    ⊣ ⦗ eis'', pis'', cis'', pgis'', fns'', cs'' ⦘
where
"⦗ cs1 , fs1 , pgi1 , ci1 , pi1 , ei1 ⦘ ⊢ d ⊣ ⦗ ei2 , pi2 , ci2 , pgi2 , fs2 , cs2 ⦘"
  := (type_topdecl cs1 fs1 pgi1 ci1 pi1 ei1 d ei2 pi2 ci2 pgi2 fs2 cs2).
(**[]*)
