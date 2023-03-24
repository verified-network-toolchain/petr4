Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4flat.Syntax.
Require Import Poulet4.P4flat.Spec.
Require Import Poulet4.P4flat.P4flatToGCL.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Import String.
Local Open Scope string_scope.

(* Dummy de bruijn index *)
Definition db := 99.
Definition one_table : P4flat.Syntax.TopDecl.prog :=
  [
    TopDecl.ControlBlock
      "C_one_table"
      [("x_one_table", PAInOut (Expr.TBit 8))]
      (Stmt.Table "t_one_table"
                  [Expr.Var (Expr.TBit 8%N) "x_one_table" db]
                  [("nop", Stmt.Skip);
                   ("set_x", Stmt.Assign (Expr.Var (Expr.TBit 8) "x_one_table" db) (Expr.Bit 8 0))]);
    TopDecl.Pkg "main" ["C_one_table"]
  ].


Definition seq_tables : P4flat.Syntax.TopDecl.prog :=
  [
    TopDecl.ControlBlock
      "C_seq_tables"
      [("x_seq_tables", PAInOut (Expr.TBit 8))]
      (Stmt.Seq
         (Stmt.Table "t1_seq_tables"
                     [Expr.Var (Expr.TBit 8%N) "x_seq_tables" db]
                     [("nop", Stmt.Skip);
                      ("set_x", Stmt.Assign (Expr.Var (Expr.TBit 8) "x_seq_tables" db) (Expr.Bit 8 0))])
         (Stmt.Table "t2_seq_tables"
                     [Expr.Var (Expr.TBit 8%N) "x_seq_tables" db]
                     [("nop", Stmt.Skip);
                      ("set_x", Stmt.Assign (Expr.Var (Expr.TBit 8) "x_seq_tables" db) (Expr.Bit 8 0))]));
    TopDecl.Pkg "main" ["C_seq_tables"]
  ].

(* List of programs (p, q, s) such that s |= p <= q *)
Definition refinements : list (TopDecl.prog * TopDecl.prog * unit) :=
  [(one_table, seq_tables, tt)].


Eval cbv in (prog_to_stmt one_table).
Eval cbv in (prog_to_stmt seq_tables).
Definition my_spec : fm (var + var) p4sig :=
  FEq (TVar (inl "x_one_table")) (TVar (inr "x_seq_tables")).
Eval cbv in (let* one := prog_to_stmt one_table in
             let* seq := prog_to_stmt seq_tables in
             ok (GCL.Dijkstra.wp _ _
                                 (GCL.Dijkstra.seq_prod_prog one seq)
                                 my_spec)).
