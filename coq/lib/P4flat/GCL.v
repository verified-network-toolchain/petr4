Require Import Coq.Strings.String.
Require Import Poulet4.P4flat.Sig.
Require Import Poulet4.P4flat.Spec.

Module Dijkstra.
  Section Dijkstra.
    Variable (var: Type).
    Variable (sig: signature).
    Inductive stmt : Type :=
    | GSkip
    | GAssign (lhs : var)
              (rhs : Spec.tm var sig)
    | GSeq (g1 g2 : stmt)
    | GChoice (g1 g2 : stmt)
    | GAssume (phi : Spec.fm var sig)
    | GAssert (phi : Spec.fm var sig).

    (* Naive WP. *)
    Fixpoint wp (s: stmt) (phi: Spec.fm var sig) : Spec.fm var sig :=
      match s with
      | GSkip => phi
      | GAssign lhs rhs => Spec.fm_subst lhs rhs phi
      | GSeq g1 g2 => wp g1 (wp g2 phi)
      | GChoice g1 g2 => FOr (wp g1 phi) (wp g2 phi)
      | GAssume psi => FImpl psi phi
      | GAssert psi => FAnd psi phi
      end.

  End Dijkstra.
  Arguments GAssign {var sig}.
  Arguments GSeq {var sig}.
  Arguments GChoice {var sig}.
  Arguments GAssume {var sig}.
  Arguments GAssert {var sig}.

  Fixpoint stmt_map_vars {V W sig} (m: V -> W) (s: stmt V sig) : stmt W sig :=
    match s with
    | GSkip _ _ => GSkip _ _
    | GAssign lhs rhs => GAssign (m lhs) (Spec.tm_map_vars m rhs)
    | GSeq g1 g2 => GSeq (stmt_map_vars m g1) (stmt_map_vars m g2) 
    | GChoice g1 g2 => GChoice (stmt_map_vars m g1) (stmt_map_vars m g2)
    | GAssume phi => GAssume (Spec.fm_map_vars m phi)
    | GAssert phi => GAssert (Spec.fm_map_vars m phi)
    end.

  (* Note this requires the two programs already agree on a signature
     [sig], but you will want them to at least have disjoint table
     signatures when dealing with table programs. *)
  Definition seq_prod_prog {V1 V2 sig}
             (s1: stmt V1 sig)
             (s2: stmt V2 sig)
    : stmt (V1 + V2) sig :=
    (* <s1|; |s2> *)
    GSeq (stmt_map_vars inl s1) (stmt_map_vars inr s2).
End Dijkstra.
