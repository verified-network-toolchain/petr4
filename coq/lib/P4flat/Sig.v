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

Section Ident.
  Context (T: Type).
  Context `{@EqDec T eq eq_equivalence}.

  Inductive ident :=
  | SSimple (base: T)
  (* length of args should always be > 0 *)
  | SIdx (base: T) (args: list nat).

  #[global]
  Instance ident_EqDec : EqDec ident eq.
  Proof.
    intros x y.
    destruct x; destruct y.
    - destruct (base == base0).
      + left.
        congruence.
      + right.
        congruence.
    - right.
      congruence.
    - right.
      congruence.
    - destruct (base == base0).
      + destruct (args == args0).
        * left.
          congruence.
        * right.
          congruence.
      + right.
        congruence.
  Defined.
End Ident.
Arguments SSimple {T}.
Arguments SIdx {T}.

Section Signature.
  Variables (sort_sym func_sym rel_sym: vocab).
  Context `{sort_eq_dec: @EqDec sort_sym eq eq_equivalence}.
  Context `{@EqDec func_sym eq eq_equivalence}.
  Context `{@EqDec rel_sym eq eq_equivalence}.

  Definition sort := ident sort_sym.
  Definition func := ident func_sym.
  Definition rel := ident rel_sym.

  Definition rank :=
    list sort.

  (* Signature without arities *)
  Record signature : Type :=
    { (* tracks arities for indexed sorts and is 0 if sort is simple *)
      sig_sorts : AList sort_sym nat eq;
      sig_funs  : func -> option (rank * sort);
      sig_rels  : rel -> option rank }.

  Definition sig_get_sort (sig: signature) (s: sort_sym) :=
    from_opt (AList.get sig.(sig_sorts) s)
             ("Sort symbol not found in sig.").

  Definition sig_get_fun (sig: signature) (f: func) :=
    from_opt (sig.(sig_funs) f)
             ("Function symbol not found in sig.").

  Definition sig_get_rel (sig: signature) (r: rel) :=
    from_opt (sig.(sig_rels) r)
             ("Relation symbol not found in sig.").

  Definition sig_check_sort (sig: signature) (s: sort) : bool :=
    match
      match s with
      | SSimple s =>
          let* idx_arity := sig_get_sort sig s in
          mret (idx_arity ==b 0)
      | SIdx s args =>
          let* idx_arity := sig_get_sort sig s in
          mret (idx_arity ==b List.length args)
      end
    with 
    | Ok b => b
    | _ => false
    end.

  (* Check that s is well-formed.
     This function should ensure that
     - sig_sorts has no duplicate sorts
     - sig_funs and sig_rels have no duplicate keys
     - The arities in s use sorts drawn only from s.(sig_sorts) *)
  Definition check_signature (sig: signature) : bool :=
    AList.key_unique sig.(sig_sorts).
End Signature.

Arguments sig_sorts {sort_sym func_sym rel_sym}.
Arguments sig_funs {sort_sym func_sym rel_sym}.
Arguments sig_rels {sort_sym func_sym rel_sym}.
Arguments sig_get_sort {sort_sym func_sym rel_sym}.
Arguments sig_check_sort {sort_sym func_sym rel_sym _}.
Arguments sig_get_fun {sort_sym func_sym rel_sym}.
Arguments sig_get_rel {sort_sym func_sym rel_sym}.
Arguments check_signature {sort_sym func_sym rel_sym _}.
