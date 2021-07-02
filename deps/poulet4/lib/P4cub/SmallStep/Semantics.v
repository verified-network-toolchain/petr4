Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.SmallStep.Value
        Poulet4.P4cub.SmallStep.Util Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Envn.

(** Notation entries. *)
Declare Custom Entry p4kstmt.

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module ST := P.Stmt.
  Module F := P.F.
  Module PT := ProperType.
  Module PR := P.Parser.
  Import P.P4cubNotations Env.EnvNotations.

  (** Continuation statements. *)
  Inductive kstmt {tags_t : Type} : Type :=
  | KStop                              (* end of continuation *)
  | KSeq (s : ST.s tags_t) (k : kstmt) (* sequencing/composition *)
  | KBlock (ϵ : @eenv tags_t) (k : kstmt)      (* block: enclosing environment & continuation *)
  | KCall (args : E.arrowE tags_t)
          (ϵ : @eenv tags_t) (k : kstmt)       (* function/procedure
                                          call-site with arguments,
                                          enclosing environment, & continuation *)
  | KExit (k : kstmt)                  (* exit statement control-flow *)
  | KReturn (o : option (E.e tags_t))
            (k : kstmt)                (* return statement control-flow *).
  (**[]*)

  Notation "'k{' s '}k'" := s (s custom p4kstmt at level 99).
  Notation "( x )" := x (in custom p4kstmt, x at level 99).
  Notation "x" := x (in custom p4kstmt at level 0, x constr at level 0).
  Notation "'κ' s '⋅' k"
    := (KSeq s k)
         (in custom p4kstmt at level 99, s custom p4stmt,
             k custom p4kstmt, right associativity).
  Notation "'∫' env '⊗' k"
    := (KBlock env k)
         (in custom p4kstmt at level 99, env custom p4env,
             k custom p4kstmt, right associativity).
  Notation "'Λ' ( args , env ) k"
    := (KCall args env k)
         (in custom p4kstmt at level 99, env custom p4env,
             k custom p4kstmt, right associativity).
  Notation "'EXIT' k"
    := (KExit k)
         (in custom p4kstmt at level 99,
             k custom p4kstmt, right associativity).
  Notation "'RETURN' o k"
    := (KReturn o k)
         (in custom p4kstmt at level 99,
             k custom p4kstmt, right associativity).
  Notation "'VOID' k"
    := (KReturn None k)
         (in custom p4kstmt at level 99,
             k custom p4kstmt, right associativity).
  Notation "'FRUIT' e k"
    := (KReturn (Some e) k)
         (in custom p4kstmt at level 99,
             k custom p4kstmt, right associativity).
  
  Reserved Notation "'ℵ' env , e1 '-->' e2"
           (at level 40, e1 custom p4expr, e2 custom p4expr).
  
  (** Expression evaluation. *)
  Inductive expr_step {tags_t : Type} (ϵ : eenv)
    : E.e tags_t -> E.e tags_t -> Prop :=
  | step_var (x : string) (τ : E.t)
             (i : tags_t) (e : E.e tags_t) :
      Env.find x ϵ = Some e ->
      ℵ ϵ, Var x:τ @ i -->  e
  | step_slice (e e' : E.e tags_t) (τ : E.t)
               (hi lo : positive) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, Slice e:τ [hi:lo] @ i -->  Slice e':τ [hi:lo] @ i
  | step_slice_eval (v v' : E.e tags_t) (τ : E.t)
                    (hi lo : positive) (i : tags_t) :
      eval_slice hi lo v = Some v' ->
      value v ->
      ℵ ϵ, Slice v:τ [hi:lo] @ i -->  v'
  | step_cast (τ : E.t) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, Cast e:τ @ i -->  Cast e':τ @ i
  | step_cast_eval (τ : E.t) (v v' : E.e tags_t) (i : tags_t) :
      eval_cast τ v = Some v' ->
      value v ->
      ℵ ϵ, Cast v:τ @ i -->  v'
  | step_uop (op : E.uop) (τ : E.t)
             (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, UOP op e:τ @ i -->  UOP op e':τ @ i
  | step_uop_eval (op : E.uop) (τ : E.t)
                  (v v' : E.e tags_t) (i : tags_t) :
      eval_uop op v = Some v' ->
      value v ->
      ℵ ϵ, UOP op v:τ @ i -->  v'
  | step_bop_l (op : E.bop) (τl τr : E.t)
               (el el' er : E.e tags_t) (i : tags_t) :
      ℵ ϵ, el -->  el' ->
           ℵ ϵ, BOP el:τl op er:τr @ i -->  BOP el':τl op er:τr @ i
  | step_bop_r (op : E.bop) (τl τr : E.t)
               (vl er er' : E.e tags_t) (i : tags_t) :
      value vl ->
      ℵ ϵ, er -->  er' ->
           ℵ ϵ, BOP vl:τl op er:τr @ i -->  BOP vl:τl op er':τr @ i
  | step_bop_eval (op : E.bop) (τl τr : E.t)
                  (vv vl vr : E.e tags_t) (i : tags_t) :
      eval_bop op vl vr i = Some vv ->
      value vl -> value vr ->
      ℵ ϵ, BOP vl:τl op vr:τr @ i -->  vv
  | step_member (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, Mem e:τ dot x @ i -->  Mem e:τ dot x @ i
  | step_member_eval (x : string) (τ : E.t)
                     (v v' : E.e tags_t) (i : tags_t) :
      eval_member x v = Some v' ->
      value v ->
      ℵ ϵ, Mem v:τ dot x @ i -->  v'
  | step_stack_access (e e' : E.e tags_t) (n : Z) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, Access e[n] @ i -->  Access e'[n] @ i
  | step_stack_access_eval (v v' : E.e tags_t) (n : Z) (i : tags_t) :
      header_stack_data v >>| fourple_4 >>=
                        (fun hs => nth_error hs (Z.to_nat n)) = Some v' ->
      value v ->
      ℵ ϵ, Access v[n] @ i -->  v'
  | step_tuple (prefix suffix : list (E.e tags_t))
               (e e' : E.e tags_t) (i : tags_t) :
      Forall value prefix ->
      ℵ ϵ, e -->  e' ->
           let es := prefix ++ e :: suffix in
           let es' := prefix ++ e' :: suffix in
           ℵ ϵ, tup es @ i -->  tup es' @ i
  | step_struct (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      F.predfs_data (value ∘ snd) prefix ->
      ℵ ϵ, e -->  e' ->
           let fs := prefix ++ (x,(τ,e)) :: suffix in
           let fs' := prefix ++ (x,(τ,e')) :: suffix in
           ℵ ϵ, struct { fs } @ i -->  struct { fs' } @ i
  | step_header (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (b e e' : E.e tags_t) (i : tags_t) :
      value b ->
      F.predfs_data (value ∘ snd) prefix ->
      ℵ ϵ, e -->  e' ->
           let fs := prefix ++ (x,(τ,e)) :: suffix in
           let fs' := prefix ++ (x,(τ,e')) :: suffix in
           ℵ ϵ, hdr { fs } valid:=b @ i -->  hdr { fs' } valid:=b @ i
  | step_header_valid (fs : F.fs string (E.t * E.e tags_t))
                      (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           ℵ ϵ, hdr { fs } valid:=e @ i -->  hdr { fs } valid:=e' @ i
  | step_header_stack (ts : F.fs string (E.t))
                      (prefix suffix : list (E.e tags_t))
                      (e e' : E.e tags_t) (size : positive)
                      (ni : Z) (i : tags_t) :
      Forall value prefix ->
      ℵ ϵ, e -->  e' ->
           let hs := prefix ++ e :: suffix in
           let hs' := prefix ++ e' :: suffix in
           ℵ ϵ, Stack hs:ts[size] nextIndex:=ni @ i -->
           Stack hs':ts[size] nextIndex:=ni @ i
  where "'ℵ' ϵ , e1 '-->' e2" := (expr_step ϵ e1 e2).
  (**[]*)

  Reserved Notation "'ℶ' e1 '-->'  e2"
           (at level 40, e1 custom p4expr, e2 custom p4expr).
  
  Inductive lvalue_step {tags_t : Type} : E.e tags_t -> E.e tags_t -> Prop :=
  | lstep_member (e e' : E.e tags_t) (τ : E.t) (x : string) (i : tags_t) :
      ℶ e -->  e' ->
      ℶ Mem e:τ dot x @ i -->   Mem e':τ dot x @ i
  | lstep_access (e e' : E.e tags_t) (idx : Z) (i : tags_t) :
      ℶ e -->  e' ->
      ℶ Access e[idx] @ i -->   Access e'[idx] @ i
  where "'ℶ' e1 '-->' e2" := (lvalue_step e1 e2).
  (**[]*)
  
  Reserved Notation "'π' envn , pe1 '-->' pe2"
           (at level 40, pe1 custom p4prsrexpr, pe2 custom p4prsrexpr).
  
  Inductive step_parser_expr {tags_t : Type} (ϵ : @eenv tags_t)
    : PR.e tags_t -> PR.e tags_t -> Prop :=
  | step_select_discriminee (e e' : E.e tags_t) (d : PR.e tags_t)
                            (cases : F.fs PR.pat (PR.e tags_t)) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
           π ϵ, select e { cases } default:=d @ i-->  select e' { cases } default:=d @ i
  | step_select_resolve (v : E.e tags_t) (d : PR.e tags_t)
                        (cases : F.fs PR.pat (PR.e tags_t)) (i : tags_t) :
      value v ->
      let pe := match F.find_value (fun _ => false) cases with (** TODO!! *)
                | None => d
                | Some pe => pe
                end in
      π ϵ, select v { cases } default:=d @ i-->  pe
  where "'π' envn , pe1 '-->' pe2"
          := (step_parser_expr envn pe1 pe2).

  Reserved Notation "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
           (at level 40, k1 custom p4kstmt, k2 custom p4kstmt,
            ϵ1 custom p4env, ϵ2 custom p4env).
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
  Inductive kstmt_step {tags_t : Type}
            (cfg : @ctrl tags_t) (tbls : @tenv tags_t) (aa : @aenv tags_t)
            (fns : fenv) (ins : @ienv tags_t) (ϵ : eenv) :
    kstmt -> kstmt -> eenv -> Prop :=
  | step_seq (s1 s2 : ST.s tags_t) (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ s1; s2 @ i ⋅ k -->  κ s1 ⋅ κ s2 ⋅ k, ϵ
  | step_skip (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ skip @ i ⋅ k -->  k, ϵ
  | step_block (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ b{ s }b ⋅ k -->  κ s ⋅ ∫ ϵ ⊗ k, ϵ
  | step_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, ∫ ϵk ⊗ k -->  k, ϵk ≪ ϵ
  | step_vardecl (τ : E.t) (x : string) (i : tags_t) (k : kstmt) :
      let v := edefault i τ in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ var x : τ @ i ⋅ k -->   k, x ↦ v;; ϵ
  | step_asgn_r (e1 e2 e2' : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e2 -->  e2' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := e2:τ @ i ⋅ k -->  κ asgn e1 := e2':τ @ i ⋅ k, ϵ
  | step_asgn_l (e1 e1' v2 : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      value v2 ->
      ℶ e1 -->  e1' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := v2:τ @ i ⋅ k -->  κ asgn e1' := v2:τ @ i ⋅ k, ϵ
  | step_asgn (v1 v2 : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      lvalue v1 ->
      value v2 ->
      let ϵ' := lv_update v1 v2 ϵ in
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ asgn v1 := v2:τ @ i ⋅ k -->  k, ϵ'
  | step_exit (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ exit @ i ⋅ k -->   EXIT k, ϵ
  | step_kexit_kseq (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT κ s ⋅ k -->  EXIT k, ϵ
  | step_kexit_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, ϵk ≪ ϵ
  | step_return_void (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ returns @ i ⋅ k -->  VOID k, ϵ
  | step_return_fruit (e e' : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return e:τ @ i ⋅ k -->  κ return e':τ @ i ⋅ k, ϵ
  | step_return_value (v : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      value v ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return v:τ @ i ⋅ k -->  FRUIT v k, ϵ
  | step_kreturn_kseq (o : option (E.e tags_t)) (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, RETURN o κ s ⋅ k -->  RETURN o k, ϵ
  | step_kreturn_kblock (o : option (E.e tags_t)) (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, ϵk ≪ ϵ
  | step_cond (e e' : E.e tags_t) (s1 s2 : ST.s tags_t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if e:Bool then s1 else s2 @ i ⋅ k -->
      κ if e:Bool then s1 else s2 @ i ⋅ k, ϵ
  | step_cond_true (s1 s2 : ST.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if TRUE @ i' :Bool then s1 else s2 @ i ⋅ k -->  κ s1 ⋅ k, ϵ
  | step_cond_false (s1 s2 : ST.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if FALSE @ i' :Bool then s1 else s2 @ i ⋅ k -->  κ s2 ⋅ k, ϵ
  | step_funcall_in_arg (prefix suffix : E.args tags_t) (f x : string)
                        (τ : E.t) (e e' : E.e tags_t)
                        (o : option (E.t * E.e tags_t))
                        (i : tags_t) (k : kstmt) :
      F.predfs_data
        (P.pred_paramarg
           (value ∘ snd) (lvalue ∘ snd)) prefix ->
      ℵ ϵ, e -->  e' ->
      let args  := prefix ++ (x, P.PAIn (τ,e))  :: suffix in
      let args' := prefix ++ (x, P.PAIn (τ,e')) :: suffix in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ funcall f with args  into o @ i ⋅ k -->
      κ funcall f with args' into o @ i ⋅ k, ϵ
   | step_funcall_lvalue (args : E.args tags_t) (f : string) (τ : E.t)
                         (e e' : E.e tags_t) (i : tags_t) (k : kstmt) :
       F.predfs_data
         (P.pred_paramarg
            (value ∘ snd) (lvalue ∘ snd)) args ->
       ℶ e -->  e' ->
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ let e:τ  := call f with args @ i ⋅ k -->
       κ let e':τ := call f with args @ i ⋅ k, ϵ
   | step_funcall (args : E.args tags_t) (f : string)
                  (o : option (E.t * E.e tags_t))
                  (i : tags_t) (k : kstmt)
                  (body : ST.s tags_t) (fϵ : eenv)
                  (fclosure : fenv) (fins : ienv) :
       lookup fns f = Some (FDecl fϵ fclosure fins body) ->
       predop (lvalue ∘ snd) o ->
       F.predfs_data
         (P.pred_paramarg
            (value ∘ snd) (lvalue ∘ snd)) args ->
       let fϵ' := copy_in args ϵ fϵ in
       let arrow := P.Arrow args o in
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ funcall f with args into o @ i ⋅ k -->
       κ body ⋅ Λ (arrow, ϵ) k, fϵ'
   | step_kexit_kcall (ϵk : eenv) (args : E.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := P.Arrow args None in
       ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT Λ (arrow, ϵk) k -->  k, ϵ'
   | step_void_kcall (ϵk : eenv) (args : E.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := P.Arrow args None in
       ℸ cfg, tbls, aa, fns, ins, ϵ, VOID Λ (arrow, ϵk) k -->  k, ϵ'
   | step_fruit_kcall (v lv : E.e tags_t) (τ : E.t) (ϵk : eenv)
                      (args : E.args tags_t) (k : kstmt) :
       let ϵ' := ϵk ▷ copy_out args ϵ ▷ lv_update lv v in
       let arrow := P.Arrow args (Some (τ, lv)) in
       ℸ cfg, tbls, aa, fns, ins, ϵ, FRUIT v Λ (arrow, ϵk) k -->  k, ϵ'
  where "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
          := (kstmt_step cfg tbls aa fns ins ϵ1 k1 k2 ϵ2).
  (**[]*)
End Step.
