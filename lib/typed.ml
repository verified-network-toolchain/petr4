include Poulet4.Typed

let eq_dir d1 d2 =
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless -> true
  | _ -> false

let expr_ctxt_of_stmt_ctxt (s: coq_StmtContext) : coq_ExprContext =
  failwith "unimplemented"

let expr_ctxt_of_decl_ctxt (s: coq_DeclContext) : coq_ExprContext =
  failwith "unimplemented"

type 'a info = 'a Types.info 

module Annotation = Types.Annotation
