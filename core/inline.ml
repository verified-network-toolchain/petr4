module I = Petr4.Info
open Petr4.Prog
open Core_kernel
open Util
module AST = Petr4.Types
module Type = Petr4.Typed
module T = Type.Type
module Info = I

(** Performs function-inlining.
  Each call to a function will be replaced
  with a fresh variable instantiated by the
  body of the function, which will be inserted
  before the statement where the former
  function call occured. *)

(** INVARIANT: There are no function declarations
 nor function calls in the resulting program. *)

(** Function definitions. *)
type fn = {
  return: T.t;
  name: AST.P4String.t;
  type_params: AST.P4String.t list;
  params: Type.Parameter.t list;
  body: Block.t }

(** Key-value map from function names to definitions.  *)
module SM = Map.Make (String)

type fmap = fn SM.t

(** Gather all function definitions and produce
  a program free of function declarations. *)
let gather (Program p : program) : fmap * program =
  p
  |> List.fold_left
    ~f:begin fun
      (fm, rev_prog : fmap * Declaration.t list)
      (d : Declaration.t) ->
        let open Declaration in
        match d with
        | _, Function
          {return; name; type_params; params; body} ->
          Map.add_exn
            ~key:(snd name)
            ~data:{return; name; type_params; params; body}
            fm,
          rev_prog
        | _ -> fm, d :: rev_prog
      end
    ~init:(SM.empty, [])
  |> Tuple.T2.map_snd ~f:begin pgm $$ List.rev end
