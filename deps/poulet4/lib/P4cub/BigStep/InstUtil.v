Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.BigStep.Value.Value
        Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.ValEnvUtil
        Poulet4.P4cub.BigStep.BSPacket.
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
  Definition ctrl : Type := Env.t string entries.
  
  (** Table environment. *)

  Definition tenv : Type := Env.t string (Control.table tags_t).

  Definition empty_tenv := Env.empty string (Control.table tags_t).

  (** Function declarations and closures. *)
  Inductive fdecl : Type :=
  | FDecl (closure : epsilon) (* value closure *)
          (fs : Env.t string fdecl) (* function closure *)
          (* (params : list string) (* function parameters*) *)
          (body : Stmt.s tags_t) (* function body *).
  (**[]*)
  
  Definition fenv : Type := Env.t string fdecl.
  Definition empty_fenv := Env.t string fdecl.
  
  (** Action declarations and closures. *)
  Inductive adecl : Type :=
  | ADecl (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (aa : Env.t string adecl) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (* (params : list string) (*action parameters *) *)
          (body : Stmt.s tags_t) (* action body *).
  (**[]*)
  
  Definition aenv : Type := Env.t string adecl.
  Definition empty_aenv := Env.empty string adecl.
  
  (** Control instances and environment. *)
  Inductive cinst : Type :=
  | CInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : Env.t string cinst) (* control instance closure *)
          (tbls : tenv) (* table closure *)
          (aa : aenv) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (apply_blk : Stmt.s tags_t)  (* control instance apply block *).
  (**[]*)
  
  Definition cienv : Type := Env.t string cinst.
  Definition empty_cienv := Env.empty string cinst.
  
  (** Parser instances. *)
  Inductive pinst : Type :=
  | PInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : Env.t string pinst) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : AST.Parser.state_block tags_t) (* start state *)
          (states : F.fs string (AST.Parser.state_block tags_t)) (* other states *).
  (**[]*)
  
  Definition pienv : Type := Env.t string pinst.
  Definition empty_pienv := Env.empty string pinst.
  
  (** Control declarations and closures. *)
  Inductive cdecl : Type :=
  | CDecl (cs : Env.t string cdecl) (* control declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : cienv) (* control instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (body : Control.d tags_t) (* declarations inside control *)
          (apply_block : Stmt.s tags_t) (* apply block *).
  (**[]*)

  Definition cenv : Type := Env.t string cdecl.
  Definition empty_cdecl := Env.t string cdecl.
  
  (** Parser declarations and closures. *)
  Inductive pdecl : Type :=
  | PDecl (ps : Env.t string pdecl) (* parser declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : pienv) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : AST.Parser.state_block tags_t) (* start state *)
          (states : F.fs string (AST.Parser.state_block tags_t)) (* parser states *).
  (**[]*)

  Definition penv : Type := Env.t string pdecl.
  Definition empty_penv := Env.empty string pdecl.

  (** Extern declarations and closures. *)
  Inductive edecl : Type :=
  | EDecl (es : Env.t string edecl)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (eis : ARCH.extern_env) (* extern instance closure *).

  Definition eenv : Type := Env.t string edecl.
  Definition empty_eenv := Env.empty string edecl.
End InstEnv.
