open Core
open Poulet4
open Cimpl

let compile_program (decls:ToP4cub.coq_DeclCtx) : (cprog,string) result = 
  Ok (Cimpl.CProgram [])
