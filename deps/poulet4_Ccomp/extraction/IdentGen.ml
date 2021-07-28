open AST
open BinNums
open BinPosDef

type generator = ident

(** val gen_init : generator **)

let gen_init =
  Coq_xH

(** val gen_next : generator -> generator * ident **)

let gen_next gen =
  ((Pos.succ gen), gen)
