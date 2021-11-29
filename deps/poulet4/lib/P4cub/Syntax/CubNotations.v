Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.AST.

(** Notation entries. *)
Declare Custom Entry p4type.
Declare Custom Entry p4constructortype.
Declare Custom Entry p4uop.
Declare Custom Entry p4bop.
Declare Custom Entry p4matchkind.
Declare Custom Entry p4expr.
Declare Custom Entry p4hsop.
Declare Custom Entry p4stmt.
Declare Custom Entry p4prsrstate.
Declare Custom Entry p4selectpattern.
Declare Custom Entry p4prsrexpr.
Declare Custom Entry p4prsrstateblock.
Declare Custom Entry p4ctrldecl.
Declare Custom Entry p4topdecl.

Module TypeNotations.
  Import Expr.
  
  Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
  Notation "( x )" := x (in custom p4type, x at level 99).
  Coercion TVar : string >-> t.
  Notation "x" := x (in custom p4type at level 0, x constr at level 0).
  Notation "'Bool'" := TBool (in custom p4type at level 0).
  Notation "'bit' < w >"
    := (TBit w)
         (in custom p4type at level 2, no associativity).
  Notation "'int' < w >"
    := (TInt w)
         (in custom p4type at level 2, no associativity).
  Notation "'error'" := TError
                          (in custom p4type at level 0,
                              no associativity).
  Notation "'matchkind'"
    := TMatchKind (in custom p4type at level 0, no associativity).
  Notation "'tuple' ts"
    := (TTuple ts) (in custom p4type at level 0, no associativity).
  Notation "'struct' { fields }"
    := (TStruct fields)
         (in custom p4type at level 6, no associativity).
  Notation "'hdr' { fields }"
    := (THeader fields)
         (in custom p4type at level 6, no associativity).
  Notation "'stack' fields [ n ]"
    := (THeaderStack fields n) (in custom p4type at level 7).
  
  Notation "'{{{' ty '}}}'" := ty (ty custom p4constructortype at level 99).
  Notation "( x )" := x (in custom p4constructortype, x at level 99).
  Notation "x"
    := x (in custom p4constructortype at level 0, x constr at level 0).
  Notation "'VType' τ"
    := (CTType τ)
         (in custom p4constructortype at level 0,
             τ custom p4type).
  Notation "'ControlType' cps res ps"
    := (CTControl cps res ps)
         (in custom p4constructortype at level 0).
  Notation "'ParserType' cps res ps"
    := (CTParser cps res ps)
         (in custom p4constructortype at level 0).
  Notation "'PackageType' cps"
    := (CTPackage cps)
         (in custom p4constructortype at level 0).
(*Notation "'Extern' cps { mthds }"
  := (CTExtern cps mthds)
  (in custom p4constructortype at level 0).*)
End TypeNotations.

Module UopNotations.
  Import Expr.
  
  Notation "'_{' u '}_'" := u (u custom p4uop at level 99).
  Notation "( x )" := x (in custom p4uop, x at level 99).
  Notation "x" := x (in custom p4uop at level 0, x constr at level 0).
  Notation "!" := Not (in custom p4uop at level 0).
  Notation "~" := BitNot (in custom p4uop at level 0).
  Notation "-" := UMinus (in custom p4uop at level 0).
  Notation "'isValid'" := IsValid (in custom p4uop at level 0).
  Notation "'setValid'" := SetValid (in custom p4uop at level 0).
  Notation "'setInValid'" := SetInValid (in custom p4uop at level 0).
  Notation "'Next'" := NextIndex (in custom p4uop at level 0).
  Notation "'Size'" := Size (in custom p4uop at level 0).
End UopNotations.

Module BopNotations.
  Import Expr.
  
  Notation "'+{' x '}+'" := x (x custom p4bop at level 99).
  Notation "( x )" := x (in custom p4bop, x at level 99).
  Notation "x" := x (in custom p4bop at level 0, x constr at level 0).
  Notation "+" := Plus (in custom p4bop at level 0).
  Notation "-" := Minus (in custom p4bop at level 0).
  Notation "'|+|'" := PlusSat (in custom p4bop at level 0).
  Notation "'|-|'" := MinusSat (in custom p4bop at level 0).
  Notation "×" := Times (in custom p4bop at level 0).
  Notation "'<<'" := Shl (in custom p4bop at level 0).
  Notation "'>>'" := Shr (in custom p4bop at level 0).
  Notation "'<='" := Le (in custom p4bop at level 0).
  Notation "'>='" := Ge (in custom p4bop at level 0).
  Notation "<" := Lt (in custom p4bop at level 0).
  Notation ">" := Gt (in custom p4bop at level 0).
  Notation "'=='" := Eq (in custom p4bop at level 0).
  Notation "'!='" := NotEq (in custom p4bop at level 0).
  Notation "&" := BitAnd (in custom p4bop at level 0).
  Notation "^" := BitXor (in custom p4bop at level 0).
  Notation "|" := BitOr (in custom p4bop at level 0).
  Notation "'&&'" := And (in custom p4bop at level 0).
  Notation "'||'" := Or (in custom p4bop at level 0).
  Notation "'++'" := PlusPlus (in custom p4bop at level 0).
End BopNotations.

Module MatchkindNotations.
  Import Expr.
  
  Notation "'M{' x '}M'" := x (x custom p4matchkind at level 99).
  Notation "( x )" := x (in custom p4matchkind, x at level 99).
  Notation "x" := x (in custom p4matchkind at level 0, x constr at level 0).
  Notation "'exact'" := MKExact (in custom p4matchkind at level 0).
  Notation "'ternary'" := MKTernary (in custom p4matchkind at level 0).
  Notation "'lpm'" := MKLpm (in custom p4matchkind at level 0).
End MatchkindNotations.

Module ExprNotations.
  Import Expr.
  
  Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
  Notation "( x )" := x (in custom p4expr, x at level 99).
  Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
  Notation "'TRUE' @ i" := (EBool true i) (in custom p4expr at level 0).
  Notation "'FALSE' @ i" := (EBool false i) (in custom p4expr at level 0).
  Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
  Notation "w 'W' n @ i" := (EBit w n i) (in custom p4expr at level 0).
  Notation "w 'S' n @ i" := (EInt w n i) (in custom p4expr at level 0).
  Notation "'Var' x : ty @ i"
    := (EVar ty x i) (in custom p4expr at level 0, no associativity).
  Notation "'Slice' n [ hi : lo ] @ i"
    := (ESlice n hi lo i)
         (in custom p4expr at level 10,
             n custom p4expr, right associativity).
  Notation "'Cast' e : τ @ i"
    := (ECast τ e i)
         (in custom p4expr at level 10, τ custom p4type,
             e custom p4expr, right associativity).
  Notation "'UOP' op x : rt  @ i"
    := (EUop rt op x i)
         (in custom p4expr at level 2,
             x custom p4expr, rt custom p4type,
             op custom p4uop, no associativity).
  Notation "'BOP' x op y ':' rt @ i"
    := (EBop rt op x y i)
         (in custom p4expr at level 10,
             rt custom p4type,
             x custom p4expr, y custom p4expr,
             op custom p4bop, left associativity).
  Notation "'tup' es @ i"
    := (ETuple es i)
         (in custom p4expr at level 0).
  Notation "'struct' { fields } @ i "
    := (EStruct fields i)
         (in custom p4expr at level 6, no associativity).
  Notation "'hdr' { fields } 'valid' ':=' b @ i "
    := (EHeader fields b i)
         (in custom p4expr at level 6,
             b custom p4expr, no associativity).
  Notation "'Mem' x 'dot' y ':' rt @ i"
    := (EExprMember rt y x i)
         (in custom p4expr at level 10, x custom p4expr,
             rt custom p4type, left associativity).
  Notation "'Error' x @ i"
    := (EError x i) (in custom p4expr at level 0, no associativity).
  Notation "'Matchkind' mk @ i"
    := (EMatchKind mk i)
         (in custom p4expr at level 0, mk custom p4matchkind, no associativity).
  Notation "'Stack' hdrs : ts 'nextIndex' ':=' ni @ i"
    := (EHeaderStack ts hdrs ni i) (in custom p4expr at level 0).
  Notation "'Access' e1 [ e2 ] : ts @ i"
    := (EHeaderStackAccess ts e1 e2 i)
         (in custom p4expr at level 10,
             e1 custom p4expr, left associativity).
End ExprNotations.

Module StmtNotations.
  Import Stmt.
  
  Notation "'<<{' sop '}>>'" := sop (sop custom p4hsop at level 99).
  Notation "( x )" := x (in custom p4hsop, x at level 99).
  Notation "x"
    := x (in custom p4hsop at level 0, x constr at level 0).
  Notation "'PUSH'" := HSPush (in custom p4hsop at level 0).
  Notation "'POP'" := HSPop (in custom p4hsop at level 0).
  Notation "'-{' stmt '}-'" := stmt (stmt custom p4stmt at level 99).
  Notation "( x )" := x (in custom p4stmt, x at level 99).
  Notation "x"
    := x (in custom p4stmt at level 0, x constr at level 0).
  Notation "'skip' @ i" := (SSkip i) (in custom p4stmt at level 0).
  Notation "s1 ; s2 @ i"
    := (SSeq s1 s2 i)
         (in custom p4stmt at level 99, s1 custom p4stmt,
             s2 custom p4stmt, right associativity).
  Notation "'b{' s '}b'"
    := (SBlock s)
         (in custom p4stmt at level 99,
             s custom p4stmt, no associativity).
  Notation "'delcare' x ':' t @ i"
    := (SVardecl x (inl t) i)
         (in custom p4stmt at level 0,
             t custom p4type, no associativity).
  Notation "'init' x ':=' e @ i"
    := (SVardecl x (inr e) i)
         (in custom p4stmt at level 0,
             e custom p4expr, no associativity).
  Notation "'var' x 'with' et @ i"
    := (SVardecl x et i)
         (in custom p4stmt at level 0, no associativity).
  Notation "'asgn' e1 ':=' e2 @ i"
    := (SAssign e1 e2 i)
         (in custom p4stmt at level 40,
             e1 custom p4expr, e2 custom p4expr,
             no associativity).
  Notation "'if' e 'then' s1 'else' s2 @ i"
    := (SConditional e s1 s2 i)
         (in custom p4stmt at level 80,
             s1 custom p4stmt, s2 custom p4stmt,
             e custom p4expr, no associativity).
  Notation "'call' f < targs > ( args ) @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := None |} i)
         (in custom p4stmt at level 0, no associativity).
  Notation "'let' e ':=' 'call' f < targs > ( args ) @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := Some e |} i)
         (in custom p4stmt at level 0,
             e custom p4expr, no associativity).
  Notation "'funcall' f < targs > ( args ) 'into' o @ i"
    := (SFunCall f targs {| paramargs := args; rtrns := o |} i)
         (in custom p4stmt at level 0, no associativity).
  Notation "'calling' a 'with' args @ i"
    := (SActCall a args i) (in custom p4stmt at level 0).
  Notation "'extern' e 'calls' f < targs > ( args ) 'gives' x @ i"
    := (SExternMethodCall e f targs {| paramargs:=args; rtrns:=x |} i)
         (in custom p4stmt at level 0, no associativity).
  Notation "'return' e @ i"
    := (SReturn e i) (in custom p4stmt at level 30, no associativity).
  Notation "'exit' @ i"
    := (SExit i) (in custom p4stmt at level 0, no associativity).
  Notation "'apply' x 'with' extargs '&' args @ i"
    := (SApply x extargs args i) (in custom p4stmt at level 0, no associativity).
  Notation "'invoke' tbl @ i"
    := (SInvoke tbl i) (in custom p4stmt at level 0).
End StmtNotations.

Module ParserNotations.
  Import Parser.
  
  Notation "'={' st '}='" := st (st custom p4prsrstate at level 99).
  Notation "( x )" := x (in custom p4prsrstate, x at level 99).
  Notation "x"
    := x (in custom p4prsrstate at level 0, x constr at level 0).
  Notation "'start'" := STStart (in custom p4prsrstate at level 0).
  Notation "'accept'" := STAccept (in custom p4prsrstate at level 0).
  Notation "'reject'" := STReject (in custom p4prsrstate at level 0).
  Notation "'δ' x" := (STName x) (in custom p4prsrstate at level 0).
  Notation "'[{' p '}]'" := p (p custom p4selectpattern at level 99).
  Notation "( x )" := x (in custom p4selectpattern, x at level 99).
  Notation "x"
    := x (in custom p4selectpattern at level 0, x constr at level 0).
  Notation "'??'" := PATWild (in custom p4selectpattern at level 0).
  Notation "w 'PW' n" := (PATBit w n) (in custom p4selectpattern at level 0).
  Notation "w 'PS' z" := (PATInt w z) (in custom p4selectpattern at level 0).
  Notation "'PTUP' ps" := (PATTuple ps) (in custom p4selectpattern at level 0).
  Notation "p1 '&&&' p2"
    := (PATMask p1 p2)
         (in custom p4selectpattern at level 10,
             p1 custom p4selectpattern, p2 custom p4selectpattern,
             right associativity).
  Notation "p1 '..' p2"
    := (PATRange p1 p2)
         (in custom p4selectpattern at level 12,
             p1 custom p4selectpattern, p2 custom p4selectpattern,
             right associativity).
  Notation "'p{' exp '}p'" := exp (exp custom p4prsrexpr at level 99).
  Notation "( x )" := x (in custom p4prsrexpr, x at level 99).
  Notation "x"
    := x (in custom p4prsrexpr at level 0, x constr at level 0).
  Notation "'goto' st @ i"
    := (PGoto st i)
         (in custom p4prsrexpr at level 0,
             st custom p4prsrstate).
  Notation "'select' exp { cases } 'default' ':=' def @ i"
    := (PSelect exp def cases i)
         (in custom p4prsrexpr at level 10,
             exp custom p4expr).
  Notation "'&{' st '}&'" := st (st custom p4prsrstateblock at level 99).
  Notation "( x )" := x (in custom p4prsrstateblock, x at level 99).
  Notation "x"
    := x (in custom p4prsrstateblock at level 0, x constr at level 0).
  Notation "'state' { s } 'transition' pe"
    := {| stmt:=s; trans:=pe |}
         (in custom p4prsrstateblock at level 0,
             s custom p4stmt, pe custom p4prsrexpr).
End ParserNotations.

Module ControlNotations.
  Import Control.
  
  Notation "'c{' decl '}c'" := decl (decl custom p4ctrldecl at level 99).
  Notation "( x )" := x (in custom p4ctrldecl, x at level 99).
  Notation "x"
    := x (in custom p4ctrldecl at level 0, x constr at level 0).
  Notation "d1 ';c;' d2 @ i"
    := (CDSeq d1 d2 i)
         (in custom p4ctrldecl at level 10,
             d1 custom p4ctrldecl, d2 custom p4ctrldecl,
             right associativity).
  Notation "'action' a ( params ) { body } @ i"
    := (CDAction a params body i)
         (in custom p4ctrldecl at level 0, body custom p4stmt).
  Notation "'table' t 'key' ':=' ems 'actions' ':=' acts @ i"
    := (CDTable t {|table_key:=ems; table_actions:=acts|} i)
         (in custom p4ctrldecl at level 0).
End ControlNotations.

Module TopDeclNotations.
  Import TopDecl.
  
  Notation "'%{' decl '}%'" := decl (decl custom p4topdecl at level 99).
  Notation "( x )" := x (in custom p4topdecl, x at level 99).
  Notation "x"
    := x (in custom p4topdecl at level 0, x constr at level 0).
  Notation "d1 ';%;' d2 @ i"
    := (TPSeq d1 d2 i)
         (in custom p4topdecl at level 10,
             d1 custom p4topdecl, d2 custom p4topdecl,
             right associativity).
  Notation "'Instance' x 'of' c < targs > ( args ) @ i"
    := (TPInstantiate c x targs args i) (in custom p4topdecl at level 0).
  Notation "'void' f < tparams > ( params ) { body } @ i"
    := (TPFunction f tparams {|paramargs:=params; rtrns:=None|} body i)
         (in custom p4topdecl at level 0, body custom p4stmt).
  Notation "'fn' f < tparams > ( params ) '->' t { body } @ i"
    := (TPFunction f tparams {|paramargs:=params; rtrns:=Some t|} body i)
         (in custom p4topdecl at level 0,
             t custom p4type, body custom p4stmt).
  Notation "'extern' e < tparams > ( cparams ) { methods } @ i"
    := (TPExtern e tparams cparams methods i)
         (in custom p4topdecl at level 0).
  Notation "'control' c ( cparams ) ( eps ) ( params ) 'apply' { blk } 'where' { body } @ i"
    := (TPControl c cparams eps params body blk i)
         (in custom p4topdecl at level 0,
             blk custom p4stmt, body custom p4ctrldecl).
  Notation "'parser' p ( cparams ) ( eps ) ( params ) 'start' ':=' st { states } @ i"
    := (TPParser p cparams eps params st states i)
         (in custom p4topdecl at level 0, st custom p4prsrstateblock).
  (*Notation "'package' p < tparams > ( cparams ) @ i"
    := (TPPackage p tparams cparams i)
         (in custom p4topdecl at level 0).*)
End TopDeclNotations.

Module AllCubNotations.
  Export TypeNotations UopNotations BopNotations
         MatchkindNotations ExprNotations StmtNotations
         ParserNotations ControlNotations TopDeclNotations.
End AllCubNotations.
