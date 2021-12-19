Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value BigStep.ValEnvUtil BigStep.BSPacket.
Import String.
Module V := Val.
Import V.ValueNotations V.LValueNotations.

Section InstEnv.
  Context {tags_t : Type}.
  
  (** Control plane table entries,
      essentially mapping tables to an action call. *)
  Definition entries : Type :=
    list (V.v * Expr.matchkind) ->
    list string ->
    string * Expr.args tags_t.
  (**[]*)
  
  (** Control plane tables. *)
  Definition ctrl : Type := Clmt.t string entries.
  
  (** Table environment. *)

  Definition tenv : Type := Clmt.t string (Control.table tags_t).

  Definition empty_tenv := Clmt.empty string (Control.table tags_t).

  (** Function declarations and closures. *)
  Inductive fdecl : Type :=
  | FDecl (closure : epsilon) (* value closure *)
          (fs : Clmt.t string fdecl) (* function closure *)
          (* (params : list string) (* function parameters*) *)
          (body : Stmt.s tags_t) (* function body *).
  (**[]*)
  
  Definition fenv : Type := Clmt.t string fdecl.
  Definition empty_fenv := Clmt.t string fdecl.
  
  (** Action declarations and closures. *)
  Inductive adecl : Type :=
  | ADecl (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (aa : Clmt.t string adecl) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (* (params : list string) (*action parameters *) *)
          (body : Stmt.s tags_t) (* action body *).
  (**[]*)
  
  Definition aenv : Type := Clmt.t string adecl.
  Definition empty_aenv := Clmt.empty string adecl.
  
  (** Control instances and environment. *)
  Inductive cinst : Type :=
  | CInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : Clmt.t string cinst) (* control instance closure *)
          (tbls : tenv) (* table closure *)
          (aa : aenv) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (apply_blk : Stmt.s tags_t)  (* control instance apply block *).
  (**[]*)
  
  Definition cienv : Type := Clmt.t string cinst.
  Definition empty_cienv := Clmt.empty string cinst.
  
  (** Parser instances. *)
  Inductive pinst : Type :=
  | PInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : Clmt.t string pinst) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : AST.Parser.state_block tags_t) (* start state *)
          (states : F.fs string (AST.Parser.state_block tags_t)) (* other states *).
  (**[]*)
  
  Definition pienv : Type := Clmt.t string pinst.
  Definition empty_pienv := Clmt.empty string pinst.
  
  (** Control declarations and closures. *)
  Inductive cdecl : Type :=
  | CDecl (cs : Clmt.t string cdecl) (* control declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : cienv) (* control instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (body : Control.d tags_t) (* declarations inside control *)
          (apply_block : Stmt.s tags_t) (* apply block *).
  (**[]*)

  Definition cenv : Type := Clmt.t string cdecl.
  Definition empty_cdecl := Clmt.t string cdecl.
  
  (** Parser declarations and closures. *)
  Inductive pdecl : Type :=
  | PDecl (ps : Clmt.t string pdecl) (* parser declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : pienv) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : AST.Parser.state_block tags_t) (* start state *)
          (states : F.fs string (AST.Parser.state_block tags_t)) (* parser states *).
  (**[]*)

  Definition penv : Type := Clmt.t string pdecl.
  Definition empty_penv := Clmt.empty string pdecl.

  (** Extern declarations and closures. *)
  Inductive edecl : Type :=
  | EDecl (es : Clmt.t string edecl)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (eis : ARCH.extern_env) (* extern instance closure *).

  Definition eenv : Type := Clmt.t string edecl.
  Definition empty_eenv := Clmt.empty string edecl.
End InstEnv.
