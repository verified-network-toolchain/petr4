Require Import Coq.Strings.String.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.P4flat.Sig.
Require Import Poulet4.P4flat.Spec.
Require Import Poulet4.Monads.Result.
Require Import Poulet4.Utils.AList.
Import ResultNotations.
Open Scope list_scope.

Section GGCL.
  Variable (var: Type).
  Context `{Equivalence var eq}.
  Context `{EqDec var eq}.
  Variables (sort_sym fun_sym rel_sym: vocab).
  Context `{@EqDec fun_sym eq eq_equivalence}.
  Context `{@EqDec rel_sym eq eq_equivalence}.
  Context `{@EqDec sort_sym eq eq_equivalence}.
  Variable (sig: signature sort_sym fun_sym rel_sym).

  Inductive stmt : Type :=
  | GSkip
  | GAssign (lhs : var)
            (rhs : Spec.tm var fun_sym)
  | GSeq (g1 g2 : stmt)
  | GChoice (g1 g2 : stmt)
  | GAssume (phi : Spec.fm var fun_sym rel_sym)
  | GAssert (phi : Spec.fm var fun_sym rel_sym).

  (* Naive WP. *)
  Fixpoint wp (s: stmt) (phi: Spec.fm var fun_sym rel_sym)
    : Spec.fm var fun_sym rel_sym :=
    match s with
    | GSkip => phi
    | GAssign lhs rhs => Spec.fm_subst lhs rhs phi
    | GSeq g1 g2 => wp g1 (wp g2 phi)
    | GChoice g1 g2 => FOr (wp g1 phi) (wp g2 phi)
    | GAssume psi => FImpl psi phi
    | GAssert psi => FAnd psi phi
    end.

End GGCL.
Arguments GAssign {var fun_sym rel_sym}.
Arguments GSeq    {var fun_sym rel_sym}.
Arguments GChoice {var fun_sym rel_sym}.
Arguments GAssume {var fun_sym rel_sym}.
Arguments GAssert {var fun_sym rel_sym}.

Fixpoint stmt_map_vars {V W fun_sym rel_sym} (m: V -> W) (s: stmt V fun_sym rel_sym)
  : stmt W fun_sym rel_sym :=
  match s with
  | GSkip _ _ _ => GSkip _ _ _
  | GAssign lhs rhs => GAssign (m lhs) (Spec.tm_map_vars m rhs)
  | GSeq g1 g2 => GSeq (stmt_map_vars m g1) (stmt_map_vars m g2) 
  | GChoice g1 g2 => GChoice (stmt_map_vars m g1) (stmt_map_vars m g2)
  | GAssume phi => GAssume (Spec.fm_map_vars m phi)
  | GAssert phi => GAssert (Spec.fm_map_vars m phi)
  end.

Fixpoint stmt_map_funs {V F G rel_sym} (m: F -> G) (s: stmt V F rel_sym)
  : stmt V G rel_sym :=
  match s with
  | GSkip _ _ _ => GSkip _ _ _
  | GAssign lhs rhs => GAssign lhs (Spec.tm_map_funs m rhs)
  | GSeq g1 g2 => GSeq (stmt_map_funs m g1) (stmt_map_funs m g2) 
  | GChoice g1 g2 => GChoice (stmt_map_funs m g1) (stmt_map_funs m g2)
  | GAssume phi => GAssume (Spec.fm_map_funs m phi)
  | GAssert phi => GAssert (Spec.fm_map_funs m phi)
  end.

Section Products.
  Context {V1: Type}.
  Context `{Equivalence V1 eq}.
  Context `{EqDec V1 eq}.
  Context {V2: Type}.
  Context `{Equivalence V2 eq}.
  Context `{EqDec V2 eq}.
  Variables (sort_sym fun_sym F1 F2 rel_sym: vocab).
  Context `{@EqDec fun_sym eq eq_equivalence}.
  Context `{@EqDec rel_sym eq eq_equivalence}.
  Context `{@EqDec sort_sym eq eq_equivalence}.
  Variable (sig: signature sort_sym fun_sym rel_sym).

  Definition alist_sum {A B V} (l1: AList A V eq) (l2: AList B V eq) : AList (A + B) V eq :=
    List.map (fun '(k, v) => (inl k, v)) l1 ++
    List.map (fun '(k, v) => (inr k, v)) l2.

  Definition fix_fun1 (f: fun_sym + F1) : fun_sym + (F1 + F2) := 
    FunUtil.map_sum id inl f.

  Definition fix_fun2 (f: fun_sym + F2) : fun_sym + (F1 + F2) := 
    FunUtil.map_sum id inr f.

  (* Note this requires the two programs already agree on a signature
     [sig], but you will want them to at least have disjoint table
     signatures when dealing with table programs. *)
  Definition seq_prod_prog
             (fsig1: AList F1 (rank sort_sym * sort sort_sym) eq)
             (gamma1: list (V1 * sort sort_sym))
             (s1: stmt V1 (fun_sym + F1)%type rel_sym)
             (fsig2: AList F2 (rank sort_sym * sort sort_sym) eq)
             (gamma2: AList V2 (sort sort_sym) eq)
             (s2: stmt V2 (fun_sym + F2)%type rel_sym)
    : AList (F1 + F2)%type (rank sort_sym * sort sort_sym) eq *
      AList (V1 + V2)%type (sort sort_sym) eq *
      stmt (V1 + V2) (fun_sym + (F1 + F2))%type rel_sym :=
    (* <s1|; |s2> *)
    (alist_sum fsig1 fsig2,
     alist_sum gamma1 gamma2,
     GSeq (stmt_map_funs fix_fun1 (stmt_map_vars inl s1))
          (stmt_map_funs fix_fun2 (stmt_map_vars inr s2))).

End Products.
