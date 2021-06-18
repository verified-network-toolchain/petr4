From compcert Require Import Clight Ctypes.
Require Import Poulet4.P4cub.Syntax.AST.

Require Import Integers Floats.
Check program.
(** P4Cub -> Clight **)
Section Ccomp.
  Context (tags_t: Type).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  Definition x : AST.ident := xH .
  (* currently just an empty program *)

  
  Definition Compile (prog: tpdecl) : Errors.res (Ctypes.program Clight.function) := 
    let main_decl : AST.globdef (fundef function) type :=
      AST.Gfun (Ctypes.Internal (Clight.mkfunction 
        Ctypes.Tvoid 
        (AST.mkcallconv None true true)
        []
        []
        []
        Sskip
      ))
    in
    let res_prog : Errors.res (program function) := make_program 
      [] [(xH, main_decl)] [] xH
    in
    res_prog.
End Ccomp.


