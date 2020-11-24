(** * Typechecking *)

From CORE Require Export AST.

(** * Expression Typechecking *)
Module CheckExpr (P4 : P4DataTypes).
  Module E := Expr P4.
  Export E.
End CheckExpr.
