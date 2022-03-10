Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.AST.
Import String.

Declare Scope cub_scope.
Delimit Scope cub_scope with cub.

Module TypeNotations.
  Import Expr.
  Coercion TVar : nat >-> t.
  Notation "'bit' < w >"
    := (TBit w)
         (at level 2, no associativity) : cub_scope.
  Notation "'int' < w >"
    := (TInt w)
         (at level 2, no associativity) : cub_scope.
  Coercion CTType : t >-> ct.
End TypeNotations.

Module ExprNotations.
  Import Expr.

  Notation "!" := Not (at level 0) : cub_scope.
  Notation "~" := BitNot (at level 0) : cub_scope.
  Notation "-" := UMinus (at level 0) : cub_scope.

  Notation "+" := Plus (at level 0) : cub_scope.
  Notation "-" := Minus (at level 0) : cub_scope.
  Notation "'|+|'" := PlusSat (at level 0) : cub_scope.
  Notation "'|-|'" := MinusSat (at level 0) : cub_scope.
  Notation "×" := Times (at level 0) : cub_scope.
  Notation "'<<'" := Shl (at level 0) : cub_scope.
  Notation "'>>'" := Shr (at level 0) : cub_scope.
  Notation "'<='" := Le (at level 0) : cub_scope.
  Notation "'>='" := Ge (at level 0) : cub_scope.
  Notation "<" := Lt (at level 0): cub_scope.
  Notation ">" := Gt (at level 0): cub_scope.
  Notation "'=='" := Eq (at level 0): cub_scope.
  Notation "'!='" := NotEq (at level 0): cub_scope.
  Notation "&" := BitAnd (at level 0): cub_scope.
  Notation "^" := BitXor (at level 0): cub_scope.
  Notation "|" := BitOr (at level 0): cub_scope.
  Notation "'&&'" := And (at level 0): cub_scope.
  Notation "'||'" := Or (at level 0): cub_scope.
  Notation "'++'" := PlusPlus (at level 0): cub_scope.
  (*Notation "w 'W' n '@' i" := (EBit w n i) (at level 0): cub_scope.
  Notation "w 'S' n '@' i" := (EInt w n i) (at level 0): cub_scope.*)
End ExprNotations.

Module StmtNotations.
  Import Stmt.
  Notation "s1 ';' s2 @ i"
    := (SSeq s1 s2 i)
         (at level 99, right associativity): cub_scope.
  Notation "'declare' x ':' t @ i"
    := (SVardecl x (inl t) i)
         (at level 0, no associativity): cub_scope.
  Notation "'init' x ':=' e @ i"
    := (SVardecl x (inr e) i)
         (at level 0, no associativity): cub_scope.
  Notation "'var' x 'with' et @ i"
    := (SVardecl x et i)
         (at level 0, no associativity): cub_scope.
  Notation "'asgn' e1 ':=' e2 @ i"
    := (SAssign e1 e2 i)
         (at level 40, no associativity): cub_scope.
  Notation "'if' e 'then' s1 'else' s2 @ i"
    := (SConditional e s1 s2 i)
         (at level 80, no associativity): cub_scope.
  Notation "'call' f < targs > ( args ) @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := None |} i)
         (at level 0, no associativity): cub_scope.
  Notation "'let' e ':=' 'call' f < targs > ( args ) @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := Some e |} i)
         ( p4stmt at level 0,
             e custom p4expr, no associativity).
  Notation "'funcall' f < targs > ( args ) 'into' o @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := o |} i)
         ( p4stmt at level 0, no associativity).
  Notation "'calling' a 'with' args @ i"
    := (SActCall a args i) ( p4stmt at level 0).
  Notation "'extern' e 'calls' f < targs > ( args ) 'gives' x @ i"
    := (SExternMethodCall e f targs {| paramargs:=args; rtrns:=x |} i)
         ( p4stmt at level 0, no associativity).
  Notation "'return' e @ i"
    := (SReturn e i) ( p4stmt at level 30, no associativity).
  Notation "'exit' @ i"
    := (SExit i) ( p4stmt at level 0, no associativity).
  Notation "'apply' x 'with' extargs '&' args @ i"
    := (SApply x extargs args i) ( p4stmt at level 0, no associativity).
  Notation "'invoke' tbl @ i"
    := (SInvoke tbl i) ( p4stmt at level 0).
End StmtNotations.

Module ParserNotations.
  Import Parser.
  
  Notation "'={' st '}='" := st (st custom p4prsrstate at level 99).
  Notation "( x )" := x ( p4prsrstate, x at level 99).
  Notation "x"
    := x ( p4prsrstate at level 0, x constr at level 0).
  Notation "'start'" := STStart ( p4prsrstate at level 0).
  Notation "'accept'" := STAccept ( p4prsrstate at level 0).
  Notation "'reject'" := STReject ( p4prsrstate at level 0).
  Notation "'δ' x" := (STName x) ( p4prsrstate at level 0).
  Notation "'[{' p '}]'" := p (p custom p4selectpattern at level 99).
  Notation "( x )" := x ( p4selectpattern, x at level 99).
  Notation "x"
    := x ( p4selectpattern at level 0, x constr at level 0).
  Notation "'??'" := PATWild ( p4selectpattern at level 0).
  Notation "w 'PW' n" := (PATBit w n) ( p4selectpattern at level 0).
  Notation "w 'PS' z" := (PATInt w z) ( p4selectpattern at level 0).
  Notation "'PTUP' ps" := (PATTuple ps) ( p4selectpattern at level 0).
  Notation "p1 '&&&' p2"
    := (PATMask p1 p2)
         ( p4selectpattern at level 10,
             p1 custom p4selectpattern, p2 custom p4selectpattern,
             right associativity).
  Notation "p1 '..' p2"
    := (PATRange p1 p2)
         ( p4selectpattern at level 12,
             p1 custom p4selectpattern, p2 custom p4selectpattern,
             right associativity).
  Notation "'p{' exp '}p'" := exp (exp custom p4prsrexpr at level 99).
  Notation "( x )" := x ( p4prsrexpr, x at level 99).
  Notation "x"
    := x ( p4prsrexpr at level 0, x constr at level 0).
  Notation "'goto' st @ i"
    := (PGoto st i)
         ( p4prsrexpr at level 0,
             st custom p4prsrstate).
  Notation "'select' exp { cases } 'default' ':=' def @ i"
    := (PSelect exp def cases i)
         ( p4prsrexpr at level 10,
             exp custom p4expr).
  Notation "'&{' st '}&'" := st (st custom p4prsrstateblock at level 99).
  Notation "( x )" := x ( p4prsrstateblock, x at level 99).
  Notation "x"
    := x ( p4prsrstateblock at level 0, x constr at level 0).
  Notation "'state' { s } 'transition' pe"
    := {| stmt:=s; trans:=pe |}
         ( p4prsrstateblock at level 0,
             s custom p4stmt, pe custom p4prsrexpr).
End ParserNotations.

Module ControlNotations.
  Import Control.
  
  Notation "'c{' decl '}c'" := decl (decl custom p4ctrldecl at level 99).
  Notation "( x )" := x ( p4ctrldecl, x at level 99).
  Notation "x"
    := x ( p4ctrldecl at level 0, x constr at level 0).
  Notation "d1 ';c;' d2 @ i"
    := (CDSeq d1 d2 i)
         ( p4ctrldecl at level 10,
             d1 custom p4ctrldecl, d2 custom p4ctrldecl,
             right associativity).
  Notation "'action' a ( params ) { body } @ i"
    := (CDAction a params body i)
         ( p4ctrldecl at level 0, body custom p4stmt).
  Notation "'table' t 'key' ':=' ems 'actions' ':=' acts @ i"
    := (CDTable t {|table_key:=ems; table_actions:=acts|} i)
         ( p4ctrldecl at level 0).
End ControlNotations.

Module TopDeclNotations.
  Import TopDecl.
  
  Notation "'%{' decl '}%'" := decl (decl custom p4topdecl at level 99).
  Notation "( x )" := x ( p4topdecl, x at level 99).
  Notation "x"
    := x ( p4topdecl at level 0, x constr at level 0).
  Notation "d1 ';%;' d2 @ i"
    := (TPSeq d1 d2 i)
         ( p4topdecl at level 10,
             d1 custom p4topdecl, d2 custom p4topdecl,
             right associativity).
  Notation "'Instance' x 'of' c < targs > ( args ) @ i"
    := (TPInstantiate c x targs args i) ( p4topdecl at level 0).
  Notation "'void' f < tparams > ( params ) { body } @ i"
    := (TPFunction f tparams {|paramargs:=params; rtrns:=None|} body i)
         ( p4topdecl at level 0, body custom p4stmt).
  Notation "'fn' f < tparams > ( params ) '->' t { body } @ i"
    := (TPFunction f tparams {|paramargs:=params; rtrns:=Some t|} body i)
         ( p4topdecl at level 0,
             t custom p4type, body custom p4stmt).
  Notation "'extern' e < tparams > ( cparams ) { methods } @ i"
    := (TPExtern e tparams cparams methods i)
         ( p4topdecl at level 0).
  Notation "'control' c ( cparams ) ( eps ) ( params ) 'apply' { blk } 'where' { body } @ i"
    := (TPControl c cparams eps params body blk i)
         ( p4topdecl at level 0,
             blk custom p4stmt, body custom p4ctrldecl).
  Notation "'parser' p ( cparams ) ( eps ) ( params ) 'start' ':=' st { states } @ i"
    := (TPParser p cparams eps params st states i)
         ( p4topdecl at level 0, st custom p4prsrstateblock).
End TopDeclNotations.

Module AllCubNotations.
  Export TypeNotations UopNotations BopNotations
         MatchkindNotations ExprNotations StmtNotations
         ParserNotations ControlNotations TopDeclNotations.
End AllCubNotations.
