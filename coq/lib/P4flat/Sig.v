Require Import Poulet4.Utils.AList.

(* a FOL signature is a: 
   1) set of sorts (e.g. Z, B, BV(n)), 
   2) function symbols indexed by argument sorts and return sort (e.g. plus: Z -> Z -> Z)
   3) relation symbols indexed by argument sorts 
*)
Definition vocab := Type.

Section Signature.
  Variables (sort_sym fun_sym rel_sym: vocab).
  (* Signature without arities *)
  Record signature : Type :=
    { sig_sorts : list sort_sym;
      sig_funs  : AList fun_sym (list sort_sym * sort_sym) eq;
      sig_rels : AList rel_sym (list sort_sym) eq }.

  (* Check that s is well-formed.
     This function should ensure that
     - sig_sorts has no duplicate sorts
     - sig_funs and sig_rels have no duplicate keys
     - The arities in s use sorts drawn only from s.(sig_sorts) *)
  Definition check_signature (s: signature) : bool :=
    true.
End Signature.

Arguments sig_sorts {sort_sym fun_sym rel_sym}.
Arguments sig_funs {sort_sym fun_sym rel_sym}.
Arguments sig_rels {sort_sym fun_sym rel_sym}.
Arguments check_signature {sort_sym fun_sym rel_sym}.
