module I = Petr4.Info
open Petr4.Prog
open Core_kernel
open Util
module AST = Petr4.Types
module Type = Petr4.Typed
module T = Type.Type
module R = Result
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
let rec gather (Program p : program) : fmap * program =
  p
  |> List.fold
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
            fm, rev_prog
        | i, Parser prsr ->
          let fm_lcl, Program lcls = gather (Program prsr.locals) in
          (* TODO: maybe need to combine names
            of different scopes more carefully.*)
          Map.merge_skewed ~combine:begin fun ~key:_ _ v -> v end fm fm_lcl,
          (i, Parser { prsr with locals = lcls }) :: rev_prog
        | i, Control ctrl ->
          let fm_lcl, Program lcls = gather (Program ctrl.locals) in
          (* TODO: maybe need to combine names
            of different scopes more carefully.*)
          Map.merge_skewed ~combine:begin fun ~key:_ _ v -> v end fm fm_lcl,
          (i, Control { ctrl with locals = lcls }) :: rev_prog
        | _ -> fm, d :: rev_prog
      end
    ~init:(SM.empty, [])
  |> Tuple.T2.map_snd ~f:begin pgm $$ List.rev end

(** Result type, either inlines all function call occurences
    or fails, primarily because a function declaration has been found. *)
type result = (program, string) R.t

(** Performs function-lining over a block. *)
let inline_blk (fm : fmap) (i, blk : Block.t) : Block.t =
  i, blk.statements
  (* TODO: fold over statements *)
  |> fun rev_stmts ->
    { blk with statements = rev_stmts }

(** Produces a program where all function calls are inlined. *)
let rec inline_decl (fm : fmap) (Program p) : result =
  p
  |> List.fold_result
       ~f:begin fun (rev_prog : Declaration.t list) (d : Declaration.t) ->
          match d with
          | _, Function _ -> R.Error "Program to inline has a function declaration."
          | i, Parser prsr ->
            let open R in
            prsr.locals
            |> pgm
            |> inline_decl fm
            >>| begin
              fun (Program lcls) ->
                (i, Declaration.Parser { prsr with locals = lcls }) :: rev_prog end
          | i, Control ctrl ->
            let open R in
            ctrl.locals
            |> pgm
            |> inline_decl fm
            >>| begin fun (Program lcls) ->
                (i, Declaration.Control
                   { ctrl with
                     locals = lcls;
                     apply = inline_blk fm ctrl.apply }) :: rev_prog end
          | _ -> failwith "TODO other cases, need an inline_expr function"
        end
       ~init:[]
   |> R.bind ~f:begin R.return $$ pgm $$ List.rev end
