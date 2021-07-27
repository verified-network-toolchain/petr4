Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.

Import Env.EnvNotations.

(** * VCS *)
Module VCGen.
  Module P := P4cub.
  Module ST := P.Stmt.
  Module E := P.Expr.
  Module F := P.F.

  Variable tags_t : Type.

  Definition and (i : tags_t) (ϕ ψ : E.e tags_t) : E.e tags_t :=
    E.EBop E.And E.TBool E.TBool ϕ ψ i.

  Definition or (i : tags_t) (ϕ ψ : E.e tags_t) : E.e tags_t :=
    E.EBop E.Or E.TBool E.TBool ϕ ψ i.

  Definition not (i : tags_t) (ϕ : E.e tags_t) : E.e tags_t :=
    E.EUop E.Not E.TBool ϕ i.

  Definition implies (i : tags_t) (ϕ ψ : E.e tags_t) : E.e tags_t :=
    or i (not i ϕ) ψ.

  (* TODO Write substitution functions*)
  Fixpoint subst_env (ε : @eenv tags_t) (e : E.e tags_t) : E.e tags_t := e.
  Fixpoint subst_expr (ϕ : E.e tags_t) (lhs rhs : E.e tags_t) : E.e tags_t := ϕ.

  Definition omap {A B : Type} (o : option A) (f : A -> B) := o >>= fun x => Some (f x).

  Infix ">>|" := omap (left associativity, at level 50).
  Infix "<$>" := option_map (right associativity, at level 60).


  (** Expression environment *)
  Definition expenv : Type := Env.t string (E.e tags_t).

  Variable (df_tag : tags_t).
  Print List.
  Fixpoint expify (v : Val.v) : (E.t * E.e tags_t) :=
    match v with
    | Val.VBool b =>
      (E.TBool, E.EBool b df_tag)
    | Val.VBit w n =>
      (E.TBit w, E.EBit w n df_tag)
    | Val.VInt w n =>
      (E.TInt w, E.EInt w n df_tag)
    | Val.VTuple vs =>
      let tes := List.map expify vs in
      let ts := List.map fst tes in
      let es := List.map snd tes in
      (E.TTuple ts, E.ETuple es df_tag)
    | Val.VStruct fs =>
      (** TODO what goes here? *)
      (E.TStruct [], E.EStruct (F.map expify fs) df_tag)
    | Val.VHeader fs b =>
      (** TODO what goes here? *)

      (E.THeader [], E.EHeader (F.map expify fs) (E.EBool b df_tag) df_tag)
    | Val.VError err =>
      (E.TError, E.EError err df_tag)
    | Val.VMatchKind mk =>
      (E.TMatchKind, E.EMatchKind mk df_tag)
    | Val.VHeaderStack fs hs n ni =>
      (* let hfs := List.map snd hs in *)
      (* let exp_inner := flip (F.fold (fun _ h l => (snd (expify h)) :: l)) [] in *)
      (* let ehs := List.fold_right (fun h => List.app (exp_inner h)) [] hfs in *)
      (* let typ_inner : F.fs string Val.v -> F.fs string E.t := *)
      (*     F.map (fun x => fst (expify x)) in *)
      (* let ths : P.F.fs string E.t  := concat (map typ_inner hfs) in *)
      (E.THeaderStack [] n, E.EHeaderStack fs [] n ni df_tag)
    end.

  
  Fixpoint expify_closure : (ε : epsilon) -> expenv :=
    List.fold (fun k ε' ->
                   match Env.find k ε with
                   | None -> ε'
                   | Some v -> !{ k -> expify v :: ε' }
              ) Env.empty (Env.keys ε)
              
  (** Create a new environment
    from a closure environment where
    values of [In] args are substituted
    into the function parameters. *)
  Definition copy_in
             (params : expenv)
             (ϵcall : epsilon) -> expenv :=
    F.fold (fun x arg ϵ =>
              match arg with
              | P.PAIn v     => !{ x ↦ v ;; ϵ }!
              | P.PAInOut lv => match lv_lookup ϵcall lv with
                                | None   => ϵ
                                | Some v => !{ x ↦ v ;; ϵ }!
                                end
              | P.PAOut _    => ϵ
              end) (expify argsv) (Env.empty).
  (**[]*)


  Fixpoint stmt_wp
           (σ : @tenv tags_t) (α : @aenv tags_t) (f : @fenv tags_t) (c : @cienv tags_t)
           (s : ST.s tags_t) (ϕ : E.e tags_t) : option (E.e tags_t) :=
    match s with
    | ST.SSkip _ => Some ϕ
    | ST.SVardecl _ _ _ =>
    (* TODO do we need to do anything here? *)
      None
    | ST.SAssign _ lhs rhs _ =>
      Some (subst_expr ϕ lhs rhs)
    | ST.SConditional _ b ct cf i =>
      stmt_wp σ α f c ct ϕ >>= fun ϕt =>
      stmt_wp σ α f c cf ϕ >>| fun ϕf =>
      and i
        (implies i b ϕt)
        (implies i (not i b) ϕf)
    | ST.SSeq s1 s2 i =>
      stmt_wp σ α f c s1 ϕ >>= stmt_wp σ α f c s2
    | ST.SBlock body =>
      stmt_wp σ α f c body ϕ
    | ST.SExternMethodCall _ _ _ _ =>
      None (* TODO implement *)
    | ST.SFunCall fname (P.Arrow pas None) i =>
      match Env.consume fname f with
      | (Some (FDecl ε fenv body), f') =>
        let ε' : expenv := copy_in pas e in
        subst_env fε' <$> stmt_wp σ α f' c body ϕ
      (* TODO The copy in-out semantics here need some thought.  *)
      | (None,_) =>
        None
      end
    | ST.SFunCall _ _ _ => None (* TODO yes? *)
    | ST.SActCall _ _ _ => None
    | ST.SReturnVoid _ => None (* TODO implement *)
    | ST.SReturnFruit _ _ _ => None (* TODO implement *)
    | ST.SExit _ => None (* TODO Implement *)
    | ST.SInvoke _ _ => None (* TODO implement *)
    | ST.SApply _ _ _ => None (* TODO implement *)
    end.
