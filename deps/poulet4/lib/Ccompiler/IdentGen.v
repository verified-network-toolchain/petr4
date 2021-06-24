From compcert Require Import AST.
Require Import Coq.PArith.BinPosDef.
Require Import List.
Section IdentGen.
 (*keep track of the highest identification number generated*)
  Definition generator : Type := ident.
  Definition gen_init : generator := xH.

  Definition gen_next (gen: generator) : (generator * ident) :=
    (Pos.succ gen, gen).
  Fixpoint gen_n_next (gen: generator) (n:nat) : (generator * list ident) :=
    match n with
    | O => (gen, nil)
    | S n' => 
      let (gen', idents') := gen_n_next gen n' in
        let (gen'', new_ident) := gen_next gen' in
        (gen'', new_ident :: idents')
    end.

End IdentGen.