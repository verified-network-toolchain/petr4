Require Export Poulet4.P4cub.Util.FunUtil
        Poulet4.P4cub.Util.ListUtil
        Poulet4.P4cub.Util.EquivUtil.

Inductive either (A B : Type) : Type :=
| Left (a : A)
| Right (b : B).
(**[]*)

Arguments Left {_ _}.
Arguments Right {_ _}.
