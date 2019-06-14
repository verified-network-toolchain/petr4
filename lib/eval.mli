module I = Info
module Info = I (* JNF: ugly hack *)
open Types
open Typed
open Env

module Eval_env: sig
  type t =     {exp: (ExpType.t * direction) env ;
                typ: ExpType.t env;
                decl: DeclType.t  env;
                value: Value.t env;
                eval_decl: Types.Declaration.t env }

  val empty_env: t

  val insert_value: t -> P4String.t -> Value.t -> t

  val insert_decls: t -> P4String.t -> Declaration.t -> t

  val find: P4String.t -> 'a Env.env -> 'a

  val find_toplevel: P4String.t -> 'a Env.env -> 'a

end

module Eval_int: sig
  val to_int: Value.t -> int

  val power2w: int -> Bigint.t
end

val eval: Types.program -> unit

val eval_expression: Env.t -> Types.Expression.t -> Value.t
