Require Import Poulet4.P4cub.Syntax.AST.
Import String.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
(*Coercion Var : nat >-> Typ.t.*)
Notation "'bit' '<' w '>'"
  := (Typ.Bit w)
       (at level 0, no associativity) : typ_scope.
Notation "'int' '<' w '>'"
  := (Typ.Int w)
       (at level 0, no associativity) : typ_scope.

Declare Scope una_scope.
Delimit Scope una_scope with una.
Notation "'`!'" := Una.Not (at level 0) : una_scope.
Notation "'`~'" := Una.BitNot (at level 0) : una_scope.
Notation "'`-'" := Una.Minus (at level 0) : una_scope.

Declare Scope bin_scope.
Delimit Scope bin_scope with bin.
Notation "'`+'" := Bin.Plus (at level 0) : bin_scope.
Notation "'`-'" := Bin.Minus (at level 0) : bin_scope.
Notation "'|+|'" := Bin.PlusSat (at level 0) : bin_scope.
Notation "'|-|'" := Bin.MinusSat (at level 0) : bin_scope.
Notation "×" := Bin.Times (at level 0) : bin_scope.
Notation "'<<'" := Bin.Shl (at level 0) : bin_scope.
Notation "'>>'" := Bin.Shr (at level 0) : bin_scope.
Notation "'≤'" := Bin.Le (at level 0) : bin_scope.
Notation "'≥'" := Bin.Ge (at level 0) : bin_scope.
Notation "'`<'" := Bin.Lt (at level 0): bin_scope.
Notation "'`>'" := Bin.Gt (at level 0): bin_scope.
Notation "'`=='" := Bin.Eq (at level 0): bin_scope.
Notation "'!='" := Bin.NotEq (at level 0): bin_scope.
Notation "&" := Bin.BitAnd (at level 0): bin_scope.
Notation "^" := Bin.BitXor (at level 0): bin_scope.
Notation "'`∣'" := Bin.BitOr (at level 0): bin_scope.
Notation "'`&&'" := Bin.And (at level 0): bin_scope.
Notation "'`||'" := Bin.Or (at level 0): bin_scope.
Notation "'`++'" := Bin.PlusPlus (at level 0): bin_scope.

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
(*Coercion Bool : bool >-> Exp.e.*)
Notation "w '`W' n" := (Exp.Bit w n) (at level 0): exp_scope.
Notation "w '`S' n" := (Exp.Int w n) (at level 0): exp_scope.
Notation "x '`[' hi ':' lo ']'"
  := (Exp.Slice x hi lo) (at level 10, left associativity) : exp_scope.

Declare Scope stm_scope.
Delimit Scope stm_scope with stm.

Notation "e1 '`:=' e2"
  := (Stm.Asgn e1 e2)
       (at level 40, no associativity): stm_scope.
Notation "'`let' x ':=' e '`in' s"
  := (Stm.LetIn x e s)
       (at level 48, right associativity): stm_scope.
Notation "s1 '`;' s2"
  := (Stm.Seq s1 s2)
       (at level 49, right associativity): stm_scope.
Notation "'`if' e '`then' s1 '`else' s2"
  := (Stm.Cond e s1 s2)
       (at level 60, no associativity): stm_scope.

(* Coercion Name : nat >-> state_label.*)
Declare Scope pat_scope.
Delimit Scope pat_scope with pat.
Notation "w 'PW' n" := (Pat.Bit w n) (at level 0, no associativity) : pat_scope.
Notation "w 'PS' z" := (Pat.Int w z) (at level 0, no associativity) : pat_scope.
Notation "p1 '..' p2"
  := (Pat.Range p1 p2)
       (at level 13, right associativity) : pat_scope.
