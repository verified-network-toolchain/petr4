Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.BigStep.Value.Value
        Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.ValEnvUtil
        Poulet4.P4cub.BigStep.BSPacket.
Module P := P4cub.
Module ST := P.Stmt.
Module CD := P.Control.ControlDecl.
Module PRSR := P.Parser.
Module V := Val.
Import V.ValueNotations V.LValueNotations.

Section InstEnv.
  Context {tags_t : Type}.
  
  (** Control plane table entries,
      essentially mapping tables to an action call. *)
  Definition entries : Type :=
    list (V.v * E.matchkind) ->
    list string ->
    string * E.args tags_t.
  (**[]*)
  
  (** Control plane tables. *)
  Definition ctrl : Type := Env.t string entries.
  
  (** Table environment. *)
  Definition tenv : Type := Env.t string (CD.table tags_t).
  
  (** Function declarations and closures. *)
  Inductive fdecl : Type :=
  | FDecl (closure : epsilon) (* value closure *)
          (fs : Env.t string fdecl) (* function closure *)
          (body : ST.s tags_t) (* function body *).
  (**[]*)
  
  Definition fenv : Type := Env.t string fdecl.
  
  (** Action declarations and closures. *)
  Inductive adecl : Type :=
  | ADecl (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (aa : Env.t string adecl) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (body : ST.s tags_t) (* action body *).
  (**[]*)
  
  Definition aenv : Type := Env.t string adecl.
  
  (** Control instances and environment. *)
  Inductive cinst : Type :=
  | CInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : Env.t string cinst) (* control instance closure *)
          (tbls : tenv) (* table closure *)
          (aa : aenv) (* action closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (apply_blk : ST.s tags_t)  (* control instance apply block *).
  (**[]*)
  
  Definition cienv : Type := Env.t string cinst.
  
  (** Parser instances. *)
  Inductive pinst : Type :=
  | PInst (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : Env.t string pinst) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : PR.state_block tags_t) (* start state *)
          (states : F.fs string (PR.state_block tags_t)) (* other states *).
  (**[]*)
  
  Definition pienv : Type := Env.t string pinst.
  
  (** Control declarations and closures. *)
  Inductive cdecl : Type :=
  | CDecl (cs : Env.t string cdecl) (* control declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (cis : cienv) (* control instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (body : CD.d tags_t) (* declarations inside control *)
          (apply_block : ST.s tags_t) (* apply block *).
  (**[]*)

  Definition cenv : Type := Env.t string cdecl.
  
  (** Parser declarations and closures. *)
  Inductive pdecl : Type :=
  | PDecl (ps : Env.t string pdecl) (* parser declaration closure *)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (pis : pienv) (* parser instance closure *)
          (eis : ARCH.extern_env) (* extern instance closure *)
          (strt : PRSR.state_block tags_t) (* start state *)
          (states : F.fs string (PRSR.state_block tags_t)) (* parser states *).
  (**[]*)

  Definition penv : Type := Env.t string pdecl.

  (** Extern declarations and closures. *)
  Inductive edecl : Type :=
  | EDecl (es : Env.t string edecl)
          (closure : epsilon) (* value closure *)
          (fs : fenv) (* function closure *)
          (eis : ARCH.extern_env) (* extern instance closure *).

  Definition eenv : Type := Env.t string edecl.
End InstEnv.
