open Core_kernel
module C = Csyntax
module Map = Map.Make(String)

type map_env = C.cexpr Map.t
type state =
  { env: map_env;
    prog: C.cprog }

let translate_expr (st: state) (e: Prog.Expression.t) =
  failwith "unimplemented"

let translate_stmt (st: state) (s: Prog.Expression.t) =
  failwith "unimplemented"

let translate_decl (st: state) (d: Prog.Declaration.t) =
  failwith "unimplemented"

let translate_prog (st: state) ((Program t): Prog.program) : state =
  List.fold ~f:translate_decl ~init:st t
