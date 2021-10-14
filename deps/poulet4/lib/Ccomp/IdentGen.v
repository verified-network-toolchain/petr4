From compcert Require Import AST Clightdefs.
Require Import Coq.PArith.BinPosDef.
Require Import List.
Require Import String.
Require Import BinaryString.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Local Open Scope string_scope.
Section IdentGen.
 (*keep track of the highest identification number generated*)
  Definition generator : Type := ident.
  Definition gen_init : generator := xH.

  Definition gen_next (gen: generator) : (generator * ident) :=
    (Pos.succ gen, $("_p_e_t_r_4_" ++ (BinaryString.of_pos gen))).
  Fixpoint gen_n_next (gen: generator) (n:nat) : (generator * list ident) :=
    match n with
    | O => (gen, nil)
    | S n' => 
      let (gen', idents') := gen_n_next gen n' in
        let (gen'', new_ident) := gen_next gen' in
        (gen'', new_ident :: idents')
    end.

End IdentGen.