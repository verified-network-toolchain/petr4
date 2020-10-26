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

(** Performs function-inlining for expressions. *)
let inline_expr (fm : fmap) (i, e : Expression.t) : Expression.t =
  let open Expression in
  match e.expr with
  | True
  | False
  | Int _
  | String _
  | Name _
  | TypeMember _
  | ErrorMember _
  | DontCare -> i, { e with expr=e.expr }
  | ArrayAccess _ -> failwith "TODO"
  | BitStringAccess _ -> failwith "TODO"
  | List _ -> failwith "TODO"
  | Record _ -> failwith "TODO"
  | UnaryOp _ -> failwith "TODO"
  | BinaryOp _ -> failwith "TODO"
  | Cast _ -> failwith "TODO"
  | ExpressionMember _ -> failwith "TODO"
  | Ternary _ -> failwith "TODO"
  | FunctionCall _ -> failwith "TODO, big kahuna"
  | NamelessInstantiation _ -> failwith "TODO"
  | Mask _ -> failwith "TODO"
  | Range _ -> failwith "TODO"

(** Performs function-inlining over a block. *)
let rec inline_blk (fm : fmap) (i, blk : Block.t) : (Block.t, string) R.t =
  let open R in
  blk.statements
  |> List.fold_result
       ~f:begin fun (rev_stmts : Statement.t list) (i, s : Statement.t) ->
          let open Statement in
          match s.stmt with
          | MethodCall {
              func = _, { expr = Name fname; typ; dir };
              type_args; args } -> failwith "TODO"
          | MethodCall _ -> R.Error "TODO better error message: expression type invalid"
          | Assignment _ -> failwith "TODO"
          | DirectApplication _ -> failwith "TODO"
          | Conditional _ -> failwith "TODO"
          | BlockStatement { block } ->
            block
            |> inline_blk fm
            >>| fun nb ->
            let new_blk = BlockStatement { block = nb } in
            (i, { s with stmt = new_blk }) :: rev_stmts
          | Exit
          | EmptyStatement -> (i, s) :: rev_stmts |> R.return
          | Return _ -> failwith "TODO"
          | Switch _ -> failwith "TODO"
          | DeclarationStatement { decl } -> failwith "TODO" end
       ~init:[]
  >>| fun rev_stmts ->
    i, { blk with statements = List.rev rev_stmts }

(** Produces a program where all function calls are inlined. *)
let rec inline_decl (fm : fmap) (Program p) : result =
  p
  |> List.fold_result
       ~f:begin fun (rev_prog : Declaration.t list) (i, d : Declaration.t) ->
          match d with
          | Function _ -> R.Error "Program to inline has a function declaration."
          | Parser prsr ->
            let open R in
            prsr.locals
            |> pgm
            |> inline_decl fm
            >>| begin
              fun (Program lcls) ->
                (i, Declaration.Parser { prsr with locals = lcls }) :: rev_prog end
          | Control ctrl ->
            let open R in
            ctrl.locals
            |> pgm
            |> inline_decl fm
            >>= begin fun (Program lcls) ->
            ctrl.apply
            |> inline_blk fm
            >>| fun iapply ->
                (i, Declaration.Control
                   { ctrl with
                     locals = lcls;
                     apply = iapply }) :: rev_prog end
          | _ -> failwith "TODO other cases, need an inline_expr function"
        end
       ~init:[]
   |> R.bind ~f:begin R.return $$ pgm $$ List.rev end
