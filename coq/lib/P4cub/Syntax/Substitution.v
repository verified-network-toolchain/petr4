From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import String.

(** * Philip Wadler style de Bruijn substitution of type variables. *)

Fixpoint tshift_typ (n : nat) (τ : Typ.t) : Typ.t :=
  match τ with
  | Typ.Bool
  | Typ.Bit _
  | Typ.Int _
  | Typ.VarBit _
  | Typ.Error       => τ
  | Typ.Var X       => Typ.Var (n + X)
  | Typ.Array s t   => Typ.Array s (tshift_typ n t)
  | Typ.Struct b ts => Typ.Struct b (map (tshift_typ n) ts)
  end.

Section Sub.
  Variable σ : nat -> Typ.t.

  Definition exts (X : nat) : Typ.t :=
    match X with
    | O => Typ.Var O
    | S n => tshift_typ 1 $ σ n
    end.

  Fixpoint tsub_typ (t : Typ.t) : Typ.t :=
    match t with
    | Typ.Bool
    | Typ.Bit _
    | Typ.Int _
    | Typ.VarBit _
    | Typ.Error       => t
    | Typ.Array n t   => Typ.Array n $ tsub_typ t
    | Typ.Struct b ts => Typ.Struct b $ List.map tsub_typ ts
    | Typ.Var X       => σ X
    end.

  Definition tsub_lists (l : Lst.t) : Lst.t :=
    match l with
    | Lst.Struct   => Lst.Struct
    | Lst.Array  t => Lst.Array $ tsub_typ t
    | Lst.Header b => Lst.Header b
    end.

  Fixpoint tsub_exp (e : Exp.t) : Exp.t :=
    match e with
    | Exp.Bool _
    | Exp.Bit _ _
    | Exp.Int _ _
    | Exp.VarBit _ _ _
    | Exp.Error _ => e
    | Exp.Var t og x       => Exp.Var (tsub_typ t) og x
    | Exp.Slice hi lo e => Exp.Slice hi lo $ tsub_exp e
    | Exp.Cast t e      => Exp.Cast (tsub_typ t) $ tsub_exp e
    | Exp.Uop rt op e   => Exp.Uop (tsub_typ rt) op $ tsub_exp e
    | Exp.Bop rt op e1 e2 =>
        Exp.Bop (tsub_typ rt) op (tsub_exp e1) $ tsub_exp e2
    | Exp.Index t e1 e2 => Exp.Index (tsub_typ t) (tsub_exp e1) $ tsub_exp e2
    | Exp.Member rt mem arg =>
        Exp.Member (tsub_typ rt) mem (tsub_exp arg)
    | Exp.Lists l es => Exp.Lists (tsub_lists l) $ map tsub_exp es
    end.
  
  Definition tsub_param
    : paramarg Typ.t Typ.t -> paramarg Typ.t Typ.t :=
    paramarg_map_same $ tsub_typ.

  Definition tsub_arg
    : paramarg Exp.t Exp.t -> paramarg Exp.t Exp.t :=
    paramarg_map_same $ tsub_exp.

  Definition tsub_trns (transition : Trns.t) :=
    match transition with
    | Trns.Direct s => Trns.Direct s
    | Trns.Select discriminee default cases =>
        Trns.Select (tsub_exp discriminee) default cases
    end.

  Definition tsub_call (fk : Call.t) : Call.t :=
    match fk with
    | Call.Funct f τs oe
      => Call.Funct f (map tsub_typ τs) $ option_map tsub_exp oe
    | Call.Action a cargs
      => Call.Action a $ map tsub_exp cargs
    | Call.Method e m τs oe
      => Call.Method e m (map tsub_typ τs) $ option_map tsub_exp oe
    | Call.Inst _ _ => fk
    end.

  Fixpoint tsub_stm (s : Stm.t) : Stm.t :=
    match s with
    | Stm.Skip
    | Stm.Exit => s
    | Stm.Ret e => Stm.Ret $ option_map tsub_exp e
    | Stm.Trans e => Stm.Trans $ tsub_trns e
    | (lhs `:= rhs)%stm
      => (tsub_exp lhs `:= tsub_exp rhs)%stm
    | Stm.Invoke e t
      => Stm.Invoke (option_map tsub_exp e) t
    | Stm.App fk args
      => Stm.App (tsub_call fk) $ map tsub_arg args
    | (`let x := e `in s)%stm
      => (`let x := map_sum tsub_typ tsub_exp e `in tsub_stm s)%stm
    | (s₁ `; s₂)%stm => (tsub_stm s₁ `; tsub_stm s₂)%stm
    | (`if g `then tru `else fls)%stm
      => (`if tsub_exp g `then tsub_stm tru `else tsub_stm fls)%stm
    end.
  
  Definition tsub_insttyp
             (ctor_type : InstTyp.t) : InstTyp.t :=
    match ctor_type with
    | InstTyp.Ctr flag extern_params params =>
        InstTyp.Ctr flag
          extern_params (map_snd tsub_param params)
    | InstTyp.Package => InstTyp.Package
    | InstTyp.Extern e => InstTyp.Extern e
    end.

  Definition tsub_arrowT
             '({| paramargs:=params; rtrns:=ret |} : Typ.arrowT) : Typ.arrowT :=
    {| paramargs := map_snd tsub_param params
    ; rtrns := option_map tsub_typ ret |}.

  Definition tsub_cparams : Top.constructor_params -> Top.constructor_params :=
    List.map (prod_map_snd tsub_insttyp).
End Sub.

Definition tsub_method
           (σ : nat -> Typ.t)
           '((Δ,xs,arr) : nat * list string * Typ.arrowT) :=
  (Δ,xs,tsub_arrowT (exts `^ Δ σ) arr).

Definition tsub_ctrl (σ : nat -> Typ.t) (d : Ctrl.t) :=
  match d with
  | Ctrl.Var og te =>
      Ctrl.Var og $ map_sum (tsub_typ σ) (tsub_exp σ) te
  | Ctrl.Action a cps dps body =>
      Ctrl.Action
        a (map_snd (tsub_typ σ) cps)
        (map_snd (tsub_param σ) dps) $ tsub_stm σ body
  | Ctrl.Table t key acts def =>
      Ctrl.Table
        t (List.map (fun '(e,mk) => (tsub_exp σ e, mk)) key)
        (List.map (fun '(a,args) => (a, map (tsub_arg σ) args)) acts)
        $ option_map (fun '(a,es) => (a, map (tsub_exp σ) es)) def
  end.

Definition tsub_top (σ : nat -> Typ.t) (d : Top.t) : Top.t :=
  match d with
  | Top.Instantiate cname iname type_args cargs expr_cargs =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := map (tsub_typ σ) type_args in
      let expr_cargs' := map (tsub_exp σ) expr_cargs in
      Top.Instantiate cname iname type_args' cargs expr_cargs'
  | Top.Extern ename tparams cparams expr_cparams methods =>
      let σ' := exts `^ tparams σ in
      let cparams' :=
        List.map (prod_map_snd $ tsub_insttyp σ') cparams in
      let expr_cparams' :=
        map (tsub_typ σ') expr_cparams in
      let methods' := Field.map (tsub_method σ') methods in
      Top.Extern ename tparams cparams' expr_cparams' methods'
  | Top.Control cname cparams expr_cparams eparams params body apply_blk =>
      let cparams' := map (prod_map_snd $ tsub_insttyp σ) cparams in
      let expr_cparams' :=
        map (tsub_typ σ) expr_cparams in
      let params' := map_snd (tsub_param σ) params in
      let body' := map (tsub_ctrl σ) body in
      let apply_blk' := tsub_stm σ apply_blk in
      Top.Control cname cparams' expr_cparams' eparams params' body' apply_blk'
  | Top.Parser pn cps expr_cparams eps ps strt sts =>
      let cps' := map (prod_map_snd $ tsub_insttyp σ) cps in
      let expr_cparams' :=
        map (tsub_typ σ) expr_cparams in
      let ps' := map_snd (tsub_param σ) ps in
      let start' := tsub_stm σ strt in
      let states' := map (tsub_stm σ) sts in
      Top.Parser pn cps' expr_cparams' eps ps' start' states'
  | Top.Funct f tparams params body =>
      let σ' := exts `^ tparams σ in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_stm σ' body in
      Top.Funct f tparams cparams' body'
  end.

(** Generate a substitution from type arguments. *)
Fixpoint gen_tsub (τs : list Typ.t) (X : nat) : Typ.t :=
  match τs, X with
  | τ :: _, O => τ
  | _ :: τs, S n => gen_tsub τs n
  | [], O => Typ.Var O
  | [], S n => Typ.Var n
  end.
