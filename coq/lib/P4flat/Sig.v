(* a FOL signature is a: 
   1) set of sorts (e.g. Z, B, BV(n)), 
   2) function symbols indexed by argument sorts and return sort (e.g. plus: Z -> Z -> Z)
   3) relation symbols indexed by argument sorts 
*)
Record signature: Type :=
  { sig_sorts: Type;
    sig_funs: Type;
    sig_rels: Type }.

Definition arity sorts := list sorts.

Record arities (s: signature) :=
  { arity_funs: s.(sig_funs) -> arity s.(sig_sorts) * s.(sig_sorts);
    arity_rels: s.(sig_rels) -> arity s.(sig_sorts) }.
