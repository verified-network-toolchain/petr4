Require Import Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     SmallStep.Value SmallStep.Util.
Import String.

(* TODO: correctly handle type parameters/arguments. *)

Module Step.
  Import Clmt.Notations.
  Open Scope climate_scope.

  (** Continuation statements. *)
  (*
  Inductive kstmt : Set :=
  | KStop                              (* end of continuation *)
  | KSeq (s : Stmt.s tags_t) (k : kstmt) (* sequencing/composition *)
  | KBlock (ϵ : lis) (k : kstmt) (* block: enclosing environment & continuation *)
  | KCall (args : Expr.arrowE tags_t)
          (ϵ : @eenv tags_t) (k : kstmt) (* function/procedure
                                          call-site with arguments,
                                          enclosing environment, & continuation *)
  | KExit (k : kstmt)                  (* exit statement control-flow *)
  | KReturn (o : option (Expr.e tags_t))
            (k : kstmt)                (* return statement control-flow *). *)
  
  Reserved Notation "⟨ env , e1 ⟩ '-->' e2"
           (at level 80, no associativity).
  
  (** Expression evaluation. *)
  Inductive exp_step (ϵ : list Exp.t) : Exp.t -> Exp.t -> Prop :=
  | step_var τ og x e :
    nth_error ϵ x = Some e ->
    ⟨ ϵ, Exp.Var τ og x ⟩ -->  e
  | step_slice e e' hi lo :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Exp.Slice hi lo e ⟩ -->  Exp.Slice hi lo e'
  | step_slice_eval v v' hi lo :
    eval_slice hi lo v = Some v' ->
    value v ->
    ⟨ ϵ, Exp.Slice hi lo v ⟩ -->  v'
  | step_cast τ e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Exp.Cast τ e ⟩ -->  Exp.Cast τ e'
  | step_cast_eval τ v v' :
    eval_cast τ v = Some v' ->
    value v ->
    ⟨ ϵ, Exp.Cast τ v ⟩ -->  v'
  | step_uop τ op e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Exp.Uop τ op e ⟩ -->  Exp.Uop τ op e'
  | step_uop_eval op τ v v' :
    eval_una op v = Some v' ->
    value v ->
    ⟨ ϵ, Exp.Uop τ op v ⟩ -->  v'
  | step_bop_l τ op el el' er :
    ⟨ ϵ, el ⟩ -->  el' ->
    ⟨ ϵ, Exp.Bop τ op el er ⟩ -->  Exp.Bop τ op el' er
  | step_bop_r τ op vl er er' :
    value vl ->
    ⟨ ϵ, er ⟩ -->  er' ->
    ⟨ ϵ, Exp.Bop τ op vl er ⟩ -->  Exp.Bop τ op vl er'
  | step_bop_eval τ op v vl vr :
    eval_bin op vl vr = Some v ->
    value vl -> value vr ->
    ⟨ ϵ, Exp.Bop τ op vl vr ⟩ -->  v
  | step_member τ x e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Exp.Member τ x e ⟩ -->  Exp.Member τ x e
  | step_member_eval τ x ls vs v :
    nth_error vs x = Some v ->
    Forall value vs ->
    ⟨ ϵ, Exp.Member τ x (Exp.Lists ls vs) ⟩ -->  v
  | step_index_l τ e₁ e₁' e₂ :
    ⟨ ϵ, e₁ ⟩ --> e₁' ->
    ⟨ ϵ, Exp.Index τ e₁ e₂ ⟩ --> Exp.Index τ e₁' e₂
  | step_index_r τ v₁ e₂ e₂' :
    value v₁ ->
    ⟨ ϵ, e₂ ⟩ --> e₂' ->
    ⟨ ϵ, Exp.Index τ v₁ e₂ ⟩ --> Exp.Index τ v₁ e₂'
  | step_index_eval τ ls vs w n v :
    nth_error vs (Z.to_nat n) = Some v ->
    Forall value vs ->
    ⟨ ϵ, Exp.Index τ (Exp.Lists ls vs) (w `W n)%exp ⟩ --> v
  | step_lists prefix suffix ls e e' :
    Forall value prefix ->
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Exp.Lists ls (prefix ++ e :: suffix) ⟩
      -->  Exp.Lists ls (prefix ++ e' :: suffix)
  where "⟨ ϵ , e1 ⟩ '-->' e2" := (exp_step ϵ e1 e2) : type_scope.

  (** TODO: add Exp.Index to this. *)
  Inductive lvalue_step : Exp.t -> Exp.t -> Prop :=
  | lstep_slice e e' hi lo :
    lvalue_step e e' ->
    lvalue_step (Exp.Slice hi lo e) (Exp.Slice hi lo e')
  | lstep_member τ x e e' :
    lvalue_step e e' ->
    lvalue_step (Exp.Member τ x e) (Exp.Member τ x e').
  
  Reserved Notation "'π' envn , pe1 '-->' pe2"
           (at level 80, no associativity).
  
  Inductive step_parser_exp (ϵ : list Exp.t)
    : Trns.t -> Trns.t -> Prop :=
  | step_select_discriminee e e' d cases :
    ⟨ ϵ, e ⟩ -->  e' ->
    π ϵ, Trns.Select e d cases -->  Trns.Select e' d cases
  | step_select_resolve v d cases :
      value v ->
      let pe := match Field.find_value (fun _ => false) cases with (** TODO!! *)
                | None => d
                | Some pe => pe
                end in
      π ϵ, Trns.Select v d cases -->  Trns.Direct pe
  where "'π' envn , pe1 '-->' pe2"
    := (step_parser_exp envn pe1 pe2).

  (*
  Reserved Notation "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
           (at level 40, k1 custom p4kstmt, k2 custom p4kstmt).
  (** TODO: Architecture & Target Issues:
      - Need a general model for architectures & targets that is both:
        + suitably abstract & parameterizable for all levels of compilation.
        + constrained enough to be useful in dynamic semantics.
      - Unsure of how to evaluate externs.
      - Unsure of packet representation.
      - Unsure of how to represent & evaluate pipeline.
      ```p4
      extern packet_in {
      void extract<T>(out T); /// reads from packet into out var
      T lookahead<T>(); /// reads from packet
      void advance(in bit<32>); /// writes to packet cursor
      bit<32> length(); /// reads from packet
      }

     extern packet_out {
            void emit<T>(in T); /// writes to output packet
     }
     ```
     Brain storm: could extern methods just be coq-functions?
     Since they are purely semantic, do I even need a consistent
     representation?

     Perhaps all IRs share some notion of "packet",
     and each IR may deal with extern-representations separately?
   *)

  (** Statement evaluation.
      This continuation-based approach
      is inspired by that of a small-step
      semantics for Cminor.
      [https://www.cs.princeton.edu/~appel/papers/seplogCminor.pdf] *)
  Variant kstmt_step {tags_t : Type}
            (cfg : @ctrl) (tbls : @tenv) (aa : @aenv)
            (fns : fenv) (ins : @ienv) (ϵ : eenv) :
    kstmt -> kstmt -> eenv -> Prop :=
  | step_seq (s1 s2 : Stmt.s)  (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ s1; s2 @ i ⋅ k -->  κ s1 ⋅ κ s2 ⋅ k, ϵ
  | step_skip  (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ skip @ i ⋅ k -->  k, ϵ
  | step_block (s : Stmt.s) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ b{ s }b ⋅ k -->  κ s ⋅ ∫ ϵ ⊗ k, ϵ
  | step_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, ∫ ϵk ⊗ k -->  k, (ϵk ≪ ϵ)
  (*| step_vardecl (τ : Typ.t) (x : string)  (k : kstmt) :
      let v := edefault i τ in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ var x : τ @ i ⋅ k -->   k, x ↦ v;; ϵ *)
  | step_asgn_r (e1 e2 e2' : Exp.t)  (k : kstmt) :
      ℵ ϵ, e2 -->  e2' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := e2 @ i ⋅ k -->  κ asgn e1 := e2' @ i ⋅ k, ϵ
  | step_asgn_l (e1 e1' v2 : Exp.t)  (k : kstmt) :
      value v2 ->
      ℶ e1 -->  e1' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := v2 @ i ⋅ k -->  κ asgn e1' := v2 @ i ⋅ k, ϵ
  | step_asgn (v1 v2 : Exp.t)  (k : kstmt) :
      lvalue v1 ->
      value v2 ->
      let ϵ' := lv_update v1 v2 ϵ in
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ asgn v1 := v2 @ i ⋅ k -->  k, ϵ'
  | step_exit  (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ exit @ i ⋅ k -->   EXIT k, ϵ
  | step_kexit_kseq (s : Stmt.s) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT κ s ⋅ k -->  EXIT k, ϵ
  | step_kexit_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, (ϵk ≪ ϵ)
  | step_return_void  (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ return None @ i ⋅ k -->  VOID k, ϵ
  | step_return_fruit (e e' : Exp.t) (τ : Typ.t)  (k : kstmt) :
      ℵ ϵ, e -->  e' ->
           let eo := Some e in
           let eo' := Some e' in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return eo @ i ⋅ k -->  κ return eo' @ i ⋅ k, ϵ
  | step_return_value (v : Exp.t) (τ : Typ.t)  (k : kstmt) :
      value v ->
      let eo := Some v in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return eo @ i ⋅ k -->  FRUIT v k, ϵ
  | step_kreturn_kseq (o : option (Exp.t)) (s : Stmt.s) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, RETURN o κ s ⋅ k -->  RETURN o k, ϵ
  | step_kreturn_kblock (o : option (Exp.t)) (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, (ϵk ≪ ϵ)
  | step_cond (e e' : Exp.t) (s1 s2 : Stmt.s)  (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if e then s1 else s2 @ i ⋅ k -->
      κ if e then s1 else s2 @ i ⋅ k, ϵ
  | step_cond_true (s1 s2 : Stmt.s) (i' i :) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if TRUE @ i' then s1 else s2 @ i ⋅ k -->  κ s1 ⋅ k, ϵ
  | step_cond_false (s1 s2 : Stmt.s) (i' i :) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if FALSE @ i' then s1 else s2 @ i ⋅ k -->  κ s2 ⋅ k, ϵ
  | step_funcall_in_arg (prefix suffix : Exp.args) (f x : string)
                        (e e' : Exp.t)
                        (o : option (Exp.t))
                         (k : kstmt) :
      F.predfs_data (pred_paramarg value lvalue) prefix ->
      ℵ ϵ, e -->  e' ->
      let args  := prefix ++ (x, PAIn e)  :: suffix in
      let args' := prefix ++ (x, PAIn e') :: suffix in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ funcall f <[]> (args)  into o @ i ⋅ k -->
      κ funcall f <[]> (args') into o @ i ⋅ k, ϵ
   | step_funcall_lvalue (args : Exp.args) (f : string)
                         (e e' : Exp.t)  (k : kstmt) :
       F.predfs_data (pred_paramarg value lvalue) args ->
       ℶ e -->  e' ->
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ let e  := call f <[]> (args) @ i ⋅ k -->
       κ let e' := call f <[]> (args) @ i ⋅ k, ϵ
   | step_funcall (args : Exp.args) (f : string)
                  (o : option (Exp.t))
                   (k : kstmt)
                  (body : Stmt.s) (fϵ : eenv)
                  (fclosure : fenv) (fins : ienv) :
       lookup fns f = Some (FDecl fϵ fclosure fins body) ->
       predop lvalue o ->
       F.predfs_data (pred_paramarg value lvalue) args ->
       let fϵ' := copy_in args ϵ fϵ in
       let arrow := {|paramargs:=args; rtrns:=o|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ funcall f <[]> (args) into o @ i ⋅ k -->
       κ body ⋅ Λ (arrow, ϵ) k, fϵ'
   | step_kexit_kcall (ϵk : eenv) (args : Exp.args) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := {|paramargs:=args; rtrns:=None|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT Λ (arrow, ϵk) k -->  k, ϵ'
   | step_void_kcall (ϵk : eenv) (args : Exp.args) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := {|paramargs:=args; rtrns:=None|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, VOID Λ (arrow, ϵk) k -->  k, ϵ'
   | step_fruit_kcall (v lv : Exp.t) (ϵk : eenv)
                      (args : Exp.args) (k : kstmt) :
       let ϵ' := ϵk ▷ copy_out args ϵ ▷ lv_update lv v in
       let arrow := {|paramargs:=args; rtrns:=Some lv|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, FRUIT v Λ (arrow, ϵk) k -->  k, ϵ'
  where "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
          := (kstmt_step cfg tbls aa fns ins ϵ1 k1 k2 ϵ2).
  (**[]*)
   *)
End Step.
