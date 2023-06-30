(*The abstract syntax tree type. *)

(* This is the internal representation of GCL which is used to pretty print to C*)

(* GCL Basic expressions : 
  | GSkip
  | GAssign (type : Typ.t) (lhs : lvalue) (rhs : rvalue)
  | GSeq (g1 g2 : t)
  | GChoice (g1 g2 : t)
  | GAssume (phi : form)
  | GAssert (phi : form)
  | GExternVoid (e : string) (args : list (form + rvalue))
  | GExternAssn (x : lvalue) (e : string) (args : list (form + rvalue))
  | GTable (tbl : string)
           (keys : list (rvalue * string))
           (actions : list (string * ((list BitVec.t) * t))).   
*)
type expr = 
| Unit (*GSkip*)

type prog = expr list 