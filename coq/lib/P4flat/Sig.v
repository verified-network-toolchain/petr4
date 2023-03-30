Require Import Coq.Classes.EquivDec.
Require Import Coq.Strings.String.
Require Import Poulet4.Utils.AList.
Require Import Poulet4.Utils.Util.ListUtil.
Require Import Poulet4.Monads.Result.

Local Open Scope string_scope.
Local Open Scope bool_scope.

(* a FOL signature is a: 
   1) set of sorts (e.g. Z, B, BV(n)), 
   2) function symbols indexed by argument sorts and return sort (e.g. plus: Z -> Z -> Z)
   3) relation symbols indexed by argument sorts 
*)
Definition vocab := Type.

Section Signature.
  Variables (sort_sym fun_sym rel_sym: vocab).
  Context `{sort_eq_dec: @EqDec sort_sym eq eq_equivalence}.
  Context `{@EqDec fun_sym eq eq_equivalence}.
  Context `{@EqDec rel_sym eq eq_equivalence}.

  (* Signature without arities *)
  Record signature : Type :=
    { sig_sorts : list sort_sym;
      sig_funs  : AList fun_sym (list sort_sym * sort_sym) eq;
      sig_rels : AList rel_sym (list sort_sym) eq }.

  Definition sig_get_sort (sig: signature) (s: sort_sym) :=
    from_opt (List.find (fun s' => s ==b s') sig.(sig_sorts))
             ("Sort symbol not found in sig.").

  Definition sig_get_fun (sig: signature) (f: fun_sym) :=
    from_opt (AList.get sig.(sig_funs) f)
             ("Function symbol not found in sig.").

  Definition sig_get_rel (sig: signature) (r: rel_sym) :=
    from_opt (AList.get sig.(sig_rels) r)
             ("Function symbol not found in sig.").

  Definition sig_check_sort (sig: signature) (s: sort_sym) : bool :=
    Result.is_okb (sig_get_sort sig s).

  (* Check that s is well-formed.
     This function should ensure that
     - sig_sorts has no duplicate sorts
     - sig_funs and sig_rels have no duplicate keys
     - The arities in s use sorts drawn only from s.(sig_sorts) *)
  Definition check_signature (sig: signature) : bool :=
    ListUtil.no_dups sort_eq_dec sig.(sig_sorts) &&
    AList.key_unique sig.(sig_funs) &&
    AList.key_unique sig.(sig_rels) &&
    List.forallb (fun '(f, (arg_sorts, ret_sort)) =>
                    List.forallb (sig_check_sort sig) arg_sorts
                    && sig_check_sort sig ret_sort)
                 sig.(sig_funs) &&
    List.forallb (fun '(r, arg_sorts) =>
                    List.forallb (sig_check_sort sig) arg_sorts)
                 sig.(sig_rels).
End Signature.

Arguments sig_sorts {sort_sym fun_sym rel_sym}.
Arguments sig_funs {sort_sym fun_sym rel_sym}.
Arguments sig_rels {sort_sym fun_sym rel_sym}.
Arguments sig_get_sort {sort_sym fun_sym rel_sym _}.
Arguments sig_check_sort {sort_sym fun_sym rel_sym _}.
Arguments sig_get_fun {sort_sym fun_sym rel_sym _}.
Arguments sig_get_rel {sort_sym fun_sym rel_sym _}.
Arguments check_signature {sort_sym fun_sym rel_sym _ _ _}.
