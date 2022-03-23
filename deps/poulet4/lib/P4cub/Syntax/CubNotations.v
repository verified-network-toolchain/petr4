Require Import Poulet4.P4cub.Syntax.AST.
Import String.

Module ExprNotations.
  Import Expr.

  Declare Scope ty_scope.
  Delimit Scope ty_scope with ty.
  Coercion TVar : nat >-> t.
  Notation "'bit' '<' w '>'"
    := (TBit w)
         (at level 0, no associativity) : ty_scope.
  Notation "'int' '<' w '>'"
    := (TInt w)
         (at level 0, no associativity) : ty_scope.

  Declare Scope uop_scope.
  Delimit Scope uop_scope with uop.
  Notation "'`!'" := Not (at level 0) : uop_scope.
  Notation "'`~'" := BitNot (at level 0) : uop_scope.
  Notation "'`-'" := UMinus (at level 0) : uop_scope.
  
  Declare Scope bop_scope.
  Delimit Scope bop_scope with bop.
  Notation "'`+'" := Plus (at level 0) : bop_scope.
  Notation "'`-'" := Minus (at level 0) : bop_scope.
  Notation "'|+|'" := PlusSat (at level 0) : bop_scope.
  Notation "'|-|'" := MinusSat (at level 0) : bop_scope.
  Notation "×" := Times (at level 0) : bop_scope.
  Notation "'<<'" := Shl (at level 0) : bop_scope.
  Notation "'>>'" := Shr (at level 0) : bop_scope.
  Notation "'≤'" := Le (at level 0) : bop_scope.
  Notation "'≥'" := Ge (at level 0) : bop_scope.
  Notation "'`<'" := Lt (at level 0): bop_scope.
  Notation "'`>'" := Gt (at level 0): bop_scope.
  Notation "'`=='" := Eq (at level 0): bop_scope.
  Notation "'!='" := NotEq (at level 0): bop_scope.
  Notation "&" := BitAnd (at level 0): bop_scope.
  Notation "^" := BitXor (at level 0): bop_scope.
  Notation "'`∣'" := BitOr (at level 0): bop_scope.
  Notation "'`&&'" := And (at level 0): bop_scope.
  Notation "'`||'" := Or (at level 0): bop_scope.
  Notation "'`++'" := PlusPlus (at level 0): bop_scope.

  Declare Scope expr_scope.
  Delimit Scope expr_scope with expr.
  Coercion Bool : bool >-> e.
  Notation "w '`W' n" := (Bit w n) (at level 0): expr_scope.
  Notation "w '`S' n" := (Int w n) (at level 0): expr_scope.
  Notation "x '`[' hi ':' lo ']'"
    := (Slice x hi lo) (at level 10, left associativity) : expr_scope.
End ExprNotations.

Module StmtNotations.
  Import Stmt.

  Declare Scope stmt_scope.
  Delimit Scope stmt_scope with stmt.
  Notation "s1 '`;' s2"
    := (Seq s1 s2)
         (at level 49, right associativity): stmt_scope.
  Notation "e1 '`:=' e2"
    := (Assign e1 e2)
         (at level 40, no associativity): stmt_scope.
  Notation "'If' e 'Then' s1 'Else' s2"
    := (Conditional e s1 s2)
         (at level 60, no associativity): stmt_scope.
End StmtNotations.

Module ParserNotations.
  Import Parser.

  Coercion Name : nat >-> state.

  Declare Scope pat_scope.
  Delimit Scope pat_scope with pat.
  Notation "w 'PW' n" := (Bit w n) (at level 0, no associativity) : pat_scope.
  Notation "w 'PS' z" := (Int w z) (at level 0, no associativity) : pat_scope.
  Notation "p1 '..' p2"
    := (Range p1 p2)
         (at level 12, right associativity) : pat_scope.
End ParserNotations.

Module ControlNotations.
  Import Control.

  Declare Scope ctrl_scope.
  Delimit Scope ctrl_scope with ctrl.
  Notation "d1 ';c;' d2"
    := (Seq d1 d2)
         (at level 20, right associativity) : ctrl_scope.
End ControlNotations.

Module TopDeclNotations.
  Import TopDecl.

  Coercion EType : Expr.t >-> it.
  Coercion CAExpr : Expr.e >-> constructor_arg.
  Declare Scope top_scope.
  Delimit Scope top_scope with top.
  Notation "d1 ';%;' d2"
    := (Seq d1 d2)
         (at level 39, right associativity) : top_scope.
End TopDeclNotations.

Module AllCubNotations.
  Export ExprNotations StmtNotations
         ParserNotations ControlNotations TopDeclNotations.
End AllCubNotations.
