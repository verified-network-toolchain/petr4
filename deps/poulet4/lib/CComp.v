From compcert Require Import Clight Ctypes.
Require Import Poulet4.P4cub.Syntax.AST.

Require Import Integers Floats.
Parameter print_Clight: Clight.program -> unit.
Check program.
(** P4Cub -> Clight **)
Section CComp.
  Context (tags_t: Type).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  (* currently just an empty program *)

  
  Definition Compile (prog: tpdecl) : Errors.res (Clight.program) := 
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

  Definition Compile_print (prog: tpdecl): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.
  
End CComp.


