Require Import Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     SmallStep.Value SmallStep.Util.
Import String.

(* TODO: correctly handle type parameters/arguments. *)

Module Step.
  Import AllCubNotations Clmt.Notations.
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
  Inductive expr_step (ϵ : list Expr.e) : Expr.e -> Expr.e -> Prop :=
  | step_var τ x e :
    nth_error ϵ x = Some e ->
    ⟨ ϵ, Expr.Var τ x ⟩ -->  e
  | step_slice e e' hi lo :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Expr.Slice e hi lo ⟩ -->  Expr.Slice e' hi lo
  | step_slice_eval v v' hi lo :
    eval_slice hi lo v = Some v' ->
    value v ->
    ⟨ ϵ, Expr.Slice v hi lo ⟩ -->  v'
  | step_cast τ e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Expr.Cast τ e ⟩ -->  Expr.Cast τ e'
  | step_cast_eval τ v v' :
    eval_cast τ v = Some v' ->
    value v ->
    ⟨ ϵ, Expr.Cast τ v ⟩ -->  v'
  | step_uop τ op e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Expr.Uop τ op e ⟩ -->  Expr.Uop τ op e'
  | step_uop_eval op τ v v' :
    eval_uop op v = Some v' ->
    value v ->
    ⟨ ϵ, Expr.Uop τ op v ⟩ -->  v'
  | step_bop_l τ op el el' er :
    ⟨ ϵ, el ⟩ -->  el' ->
    ⟨ ϵ, Expr.Bop τ op el er ⟩ -->  Expr.Bop τ op el' er
  | step_bop_r τ op vl er er' :
    value vl ->
    ⟨ ϵ, er ⟩ -->  er' ->
    ⟨ ϵ, Expr.Bop τ op vl er ⟩ -->  Expr.Bop τ op vl er'
  | step_bop_eval τ op v vl vr :
    eval_bop op vl vr = Some v ->
    value vl -> value vr ->
    ⟨ ϵ, Expr.Bop τ op vl vr ⟩ -->  v
  | step_member τ x e e' :
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Expr.Member τ x e ⟩ -->  Expr.Member τ x e
  | step_member_eval τ x vs v ob :
    nth_error vs x = Some v ->
    Forall value vs ->
    ⟨ ϵ, Expr.Member τ x (Expr.Struct vs ob) ⟩ -->  v
  | step_struct prefix suffix e e' ob :
    Forall value prefix ->
    ⟨ ϵ, e ⟩ -->  e' ->
    ⟨ ϵ, Expr.Struct (prefix ++ e :: suffix) ob ⟩
      -->  Expr.Struct (prefix ++ e' :: suffix) ob
  where "⟨ ϵ , e1 ⟩ '-->' e2" := (expr_step ϵ e1 e2) : type_scope.

  Reserved Notation "e1 '-->l' e2"
           (at level 80, no associativity).
  
  Inductive lvalue_step : Expr.e -> Expr.e -> Prop :=
  | lstep_slice e e' hi lo :
    e --> l e' ->
    Expr.Slice e hi lo --> l Expr.Slice e' hi lo
  | lstep_member τ x e e' :
    e --> l e' ->
    Expr.Member τ x e --> l Expr.Member τ x e'
  where "e1 '-->l' e2" := (lvalue_step e1 e2) : type_scope.
  
  Reserved Notation "'π' envn , pe1 '-->' pe2"
           (at level 40, pe1 custom p4prsrexpr, pe2 custom p4prsrexpr).
  
  Inductive step_parser_expr {tags_t : Type} (ϵ : @eenv tags_t)
    : AST.Parser.e tags_t -> AST.Parser.e tags_t -> Prop :=
  | step_select_discriminee (e e' : Expr.e) (d : AST.Parser.e tags_t)
                            (cases : F.fs AST.Parser.pat (AST.Parser.e tags_t)) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           π ϵ, select e { cases } default:=d @ i-->  select e' { cases } default:=d @ i
  | step_select_resolve (v : Expr.e) (d : AST.Parser.e tags_t)
                        (cases : F.fs AST.Parser.pat (AST.Parser.e tags_t)) (i : tags_t) :
      value v ->
      let pe := match F.find_value (fun _ => false) cases with (** TODO!! *)
                | None => d
                | Some pe => pe
                end in
      π ϵ, select v { cases } default:=d @ i-->  pe
  where "'π' envn , pe1 '-->' pe2"
          := (step_parser_expr envn pe1 pe2).

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
            (cfg : @ctrl tags_t) (tbls : @tenv tags_t) (aa : @aenv tags_t)
            (fns : fenv) (ins : @ienv tags_t) (ϵ : eenv) :
    kstmt -> kstmt -> eenv -> Prop :=
  | step_seq (s1 s2 : Stmt.s tags_t) (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ s1; s2 @ i ⋅ k -->  κ s1 ⋅ κ s2 ⋅ k, ϵ
  | step_skip (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ skip @ i ⋅ k -->  k, ϵ
  | step_block (s : Stmt.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ b{ s }b ⋅ k -->  κ s ⋅ ∫ ϵ ⊗ k, ϵ
  | step_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, ∫ ϵk ⊗ k -->  k, (ϵk ≪ ϵ)
  (*| step_vardecl (τ : Expr.t) (x : string) (i : tags_t) (k : kstmt) :
      let v := edefault i τ in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ var x : τ @ i ⋅ k -->   k, x ↦ v;; ϵ *)
  | step_asgn_r (e1 e2 e2' : Expr.e) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e2 -->  e2' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := e2 @ i ⋅ k -->  κ asgn e1 := e2' @ i ⋅ k, ϵ
  | step_asgn_l (e1 e1' v2 : Expr.e) (i : tags_t) (k : kstmt) :
      value v2 ->
      ℶ e1 -->  e1' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := v2 @ i ⋅ k -->  κ asgn e1' := v2 @ i ⋅ k, ϵ
  | step_asgn (v1 v2 : Expr.e) (i : tags_t) (k : kstmt) :
      lvalue v1 ->
      value v2 ->
      let ϵ' := lv_update v1 v2 ϵ in
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ asgn v1 := v2 @ i ⋅ k -->  k, ϵ'
  | step_exit (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ exit @ i ⋅ k -->   EXIT k, ϵ
  | step_kexit_kseq (s : Stmt.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT κ s ⋅ k -->  EXIT k, ϵ
  | step_kexit_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, (ϵk ≪ ϵ)
  | step_return_void (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ return None @ i ⋅ k -->  VOID k, ϵ
  | step_return_fruit (e e' : Expr.e) (τ : Expr.t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
           let eo := Some e in
           let eo' := Some e' in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return eo @ i ⋅ k -->  κ return eo' @ i ⋅ k, ϵ
  | step_return_value (v : Expr.e) (τ : Expr.t) (i : tags_t) (k : kstmt) :
      value v ->
      let eo := Some v in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return eo @ i ⋅ k -->  FRUIT v k, ϵ
  | step_kreturn_kseq (o : option (Expr.e)) (s : Stmt.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, RETURN o κ s ⋅ k -->  RETURN o k, ϵ
  | step_kreturn_kblock (o : option (Expr.e)) (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, (ϵk ≪ ϵ)
  | step_cond (e e' : Expr.e) (s1 s2 : Stmt.s tags_t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if e then s1 else s2 @ i ⋅ k -->
      κ if e then s1 else s2 @ i ⋅ k, ϵ
  | step_cond_true (s1 s2 : Stmt.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if TRUE @ i' then s1 else s2 @ i ⋅ k -->  κ s1 ⋅ k, ϵ
  | step_cond_false (s1 s2 : Stmt.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if FALSE @ i' then s1 else s2 @ i ⋅ k -->  κ s2 ⋅ k, ϵ
  | step_funcall_in_arg (prefix suffix : Expr.args tags_t) (f x : string)
                        (e e' : Expr.e)
                        (o : option (Expr.e))
                        (i : tags_t) (k : kstmt) :
      F.predfs_data (pred_paramarg value lvalue) prefix ->
      ℵ ϵ, e -->  e' ->
      let args  := prefix ++ (x, PAIn e)  :: suffix in
      let args' := prefix ++ (x, PAIn e') :: suffix in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ funcall f <[]> (args)  into o @ i ⋅ k -->
      κ funcall f <[]> (args') into o @ i ⋅ k, ϵ
   | step_funcall_lvalue (args : Expr.args tags_t) (f : string)
                         (e e' : Expr.e) (i : tags_t) (k : kstmt) :
       F.predfs_data (pred_paramarg value lvalue) args ->
       ℶ e -->  e' ->
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ let e  := call f <[]> (args) @ i ⋅ k -->
       κ let e' := call f <[]> (args) @ i ⋅ k, ϵ
   | step_funcall (args : Expr.args tags_t) (f : string)
                  (o : option (Expr.e))
                  (i : tags_t) (k : kstmt)
                  (body : Stmt.s tags_t) (fϵ : eenv)
                  (fclosure : fenv) (fins : ienv) :
       lookup fns f = Some (FDecl fϵ fclosure fins body) ->
       predop lvalue o ->
       F.predfs_data (pred_paramarg value lvalue) args ->
       let fϵ' := copy_in args ϵ fϵ in
       let arrow := {|paramargs:=args; rtrns:=o|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ funcall f <[]> (args) into o @ i ⋅ k -->
       κ body ⋅ Λ (arrow, ϵ) k, fϵ'
   | step_kexit_kcall (ϵk : eenv) (args : Expr.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := {|paramargs:=args; rtrns:=None|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT Λ (arrow, ϵk) k -->  k, ϵ'
   | step_void_kcall (ϵk : eenv) (args : Expr.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := {|paramargs:=args; rtrns:=None|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, VOID Λ (arrow, ϵk) k -->  k, ϵ'
   | step_fruit_kcall (v lv : Expr.e) (ϵk : eenv)
                      (args : Expr.args tags_t) (k : kstmt) :
       let ϵ' := ϵk ▷ copy_out args ϵ ▷ lv_update lv v in
       let arrow := {|paramargs:=args; rtrns:=Some lv|} in
       ℸ cfg, tbls, aa, fns, ins, ϵ, FRUIT v Λ (arrow, ϵk) k -->  k, ϵ'
  where "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
          := (kstmt_step cfg tbls aa fns ins ϵ1 k1 k2 ϵ2).
  (**[]*)
End Step.
