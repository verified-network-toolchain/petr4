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
Definition one_table : P4flat.Syntax.Top.prog :=
  [
    Top.ControlBlock
      "C_one_table"
      []
      [("x_one_table", PAInOut (Typ.Bit 8))]
      (Stm.Invoke None "t_one_table"
                  [Exp.Var (Typ.Bit 8%N) "x_one_table" 0]
                  [("nop", [], Stm.Skip);
                   ("set_x", [], Stm.Asgn (Exp.Var (Typ.Bit 8) "x_one_table" 0) (Exp.Bit 8 0))]);
    Top.Pkg "main" ["C_one_table"]
  ].


Definition seq_tables : P4flat.Syntax.Top.prog :=
  [
    Top.ControlBlock
      "C_seq_tables"
      []
      [("x_seq_tables", PAInOut (Typ.Bit 8))]
      (Stm.Seq
         (Stm.Invoke None "t1_seq_tables"
                     [Exp.Var (Typ.Bit 8%N) "x_seq_tables" 0]
                     [("nop", [], Stm.Skip);
                      ("set_x", [], Stm.Asgn (Exp.Var (Typ.Bit 8) "x_seq_tables" 0) (Exp.Bit 8 0))])
         (Stm.Invoke None "t2_seq_tables"
                     [Exp.Var (Typ.Bit 8%N) "x_seq_tables" 0]
                     [("nop", [], Stm.Skip);
                      ("set_x", [], Stm.Asgn (Exp.Var (Typ.Bit 8) "x_seq_tables" 0) (Exp.Bit 8 0))]));
    Top.Pkg "main" ["C_seq_tables"]
  ].

(* List of programs (p, q, s) such that s |= p <= q *)
Definition refinements : list (Top.prog * Top.prog * fm (var + var) p4funs p4rels) :=
  [(one_table, seq_tables, FEq (TVar (inl "x_one_table")) (TVar (inr "x_seq_tables")))].

Eval cbv in (prog_to_stmt one_table).
Eval cbv in (prog_to_stmt seq_tables).
Definition my_spec : fm (var + var) p4funs p4rels :=
  FEq (TVar (inl "x_one_table")) (TVar (inr "x_seq_tables")).
Eval cbv in (let comp :=
               let* one := prog_to_stmt one_table in
               let* seq := prog_to_stmt seq_tables in
               mret (GGCL.Dijkstra.wp _ _ _
                                      (GGCL.Dijkstra.seq_prod_prog _ _ one seq)
                                      my_spec)
             in
             comp).
