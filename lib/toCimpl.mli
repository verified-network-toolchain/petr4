open Poulet4

type error =
  | NotFound of string
  | V1Model of string

val string_of_error : error -> string

val compile_program : ToP4cub.coq_DeclCtx -> (Cimpl.cprog,error) Core.Result.t

