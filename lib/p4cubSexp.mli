open Sexplib

(** [sexp_of_prog prog] is the s-expression serialization of p4cub program [prog] *)
val sexp_of_prog : Poulet4.AST.TopDecl.prog -> Sexp.t
