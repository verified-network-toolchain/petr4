open Sexplib

val sexp_of_prog : Poulet4.AST.Top.prog -> Sexp.t
(** [sexp_of_prog prog] is the s-expression serialization of p4cub program
    [prog] *)

val print : Format.formatter -> Poulet4.AST.Top.prog -> unit
(** [print fmt prog] prints an s-expression representation of program [prog] 
    to [fmt] *)

val sexp_of_exp : Poulet4.AST.Exp.t -> Sexp.t
(** [sexp_of_exp exp] is the s-expression serialziation of p4cub expression
    exp*)
