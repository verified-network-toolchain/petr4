Require Import Coq.Strings.String.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.P4flat.Sig.
Require Import Poulet4.P4flat.Spec.
Require Import Poulet4.Monads.Result.
Import ResultNotations.

Module Dijkstra.
  Section Dijkstra.
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

  End Dijkstra.
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

  Section Products.
    Context {V1: Type}.
    Context `{Equivalence V1 eq}.
    Context `{EqDec V1 eq}.
    Context {V2: Type}.
    Context `{Equivalence V2 eq}.
    Context `{EqDec V2 eq}.
    Variables (sort_sym fun_sym rel_sym: vocab).
    Context `{@EqDec fun_sym eq eq_equivalence}.
    Context `{@EqDec rel_sym eq eq_equivalence}.
    Context `{@EqDec sort_sym eq eq_equivalence}.
    Variable (sig: signature sort_sym fun_sym rel_sym).

    (* Note this requires the two programs already agree on a signature
       [sig], but you will want them to at least have disjoint table
       signatures when dealing with table programs. *)
    Definition seq_prod_prog
               (s1: stmt V1 fun_sym rel_sym)
               (s2: stmt V2 fun_sym rel_sym)
      : stmt (V1 + V2) fun_sym rel_sym :=
      (* <s1|; |s2> *)
      GSeq (stmt_map_vars inl s1) (stmt_map_vars inr s2).

    Definition seq_prod_wp
               (s1: stmt V1 fun_sym rel_sym)
               (s2: stmt V2 fun_sym rel_sym)
               spec :=
      wp _ _ _ (seq_prod_prog s1 s2) spec.

  End Products.
End Dijkstra.
