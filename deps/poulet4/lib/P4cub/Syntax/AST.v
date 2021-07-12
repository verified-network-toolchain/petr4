Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt Poulet4.P4Arith
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.

(** Notation entries. *)
Declare Custom Entry p4type.
Declare Custom Entry p4constructortype.
Declare Custom Entry p4uop.
Declare Custom Entry p4bop.
Declare Custom Entry p4matchkind.
Declare Custom Entry p4expr.
Declare Custom Entry p4stmt.
Declare Custom Entry p4prsrstate.
Declare Custom Entry p4selectpattern.
Declare Custom Entry p4prsrexpr.
Declare Custom Entry p4prsrstateblock.
Declare Custom Entry p4ctrldecl.
Declare Custom Entry p4topdecl.

(** * P4cub AST *)
Module P4cub.
  Module F := Field.

  (** Function call parameters/arguments. *)
  Inductive paramarg (A B : Type) : Type :=
  | PAIn (a : A)
  | PAOut (b : B)
  | PAInOut (b : B).

  Arguments PAIn {_} {_}.
  Arguments PAOut {_} {_}.
  Arguments PAInOut {_} {_}.

  Definition paramarg_map {A B C D : Type}
             (f : A -> C) (g : B -> D)
             (pa : paramarg A B) : paramarg C D :=
    match pa with
    | PAIn a => PAIn (f a)
    | PAOut b => PAOut (g b)
    | PAInOut b => PAInOut (g b)
    end.
  (**[]*)

  (** A predicate on a [paramarg]. *)
  Definition pred_paramarg {A B : Type}
             (PA : A -> Prop) (PB : B -> Prop) (pa : paramarg A B) : Prop :=
    match pa with
    | PAIn a => PA a
    | PAOut b | PAInOut b => PB b
    end.
  (**[]*)

  Definition pred_paramarg_same {A : Type} (P : A -> Prop)
    : paramarg A A -> Prop := pred_paramarg P P.
  (**[]*)

  (** Relating [paramarg]s. *)
  Definition rel_paramarg {A1 A2 B1 B2 : Type}
             (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
             (pa1 : paramarg A1 B1)
             (pa2 : paramarg A2 B2) : Prop :=
    match pa1, pa2 with
    | PAIn a1, PAIn a2       => RA a1 a2
    | PAOut b1, PAOut b2
    | PAInOut b1, PAInOut b2 => RB b1 b2
    | _, _ => False
    end.
  (**[]*)

  Definition rel_paramarg_same {A B : Type} (R : A -> B -> Prop) :
    paramarg A A -> paramarg B B -> Prop :=
    rel_paramarg R R.
  (**[]*)

  (** Function signatures/instantiations. *)
  Inductive arrow (K A B R : Type) : Type :=
    Arrow (pas : F.fs K (paramarg A B)) (returns : option R).
  (**[]*)

  Arguments Arrow {_} {_} {_} {_}.

  (** * Expression Grammar *)
  Module Expr.
    Section P4Types.
      (** Expression types. *)
      Inductive t : Type :=
      | TBool                            (* bool *)
      | TBit (width : positive)          (* unsigned integers *)
      | TInt (width : positive)          (* signed integers *)
      | TError                           (* the error type *)
      | TMatchKind                       (* the matchkind type *)
      | TTuple (types : list t)          (* tuple type *)
      | TStruct (fields : F.fs string t) (* the struct and struct type *)
      | THeader (fields : F.fs string t) (* the header type *)
      | THeaderStack (fields : F.fs string t)
                     (size : positive)   (* header stack type *).
      (**[]*)
     

      (** Function parameters. *)
      Definition params : Type := F.fs string (paramarg t t).

      (** Function types. *)
      Definition arrowT : Type := arrow string t t t.

      (** Constructor Types. *)
      Inductive ct : Type :=
      | CTType (type : t)                   (* expression types *)
      | CTControl (cparams : F.fs string ct)
                  (parameters : params)     (* control types *)
      | CTParser (cparams : F.fs string ct)
                 (parameters : params)      (* parser types *)
      | CTPackage (cparams : F.fs string ct) (* package types *)
      | CTExtern (cparams : F.fs string ct)
                 (methods : F.fs string arrowT) (* extern types *).
      (**[]*)

      Definition constructor_params : Type := F.fs string ct.
    End P4Types.

    Module TypeNotations.
      Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
      Notation "( x )" := x (in custom p4type, x at level 99).
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
      Notation "x" := x (in custom p4constructortype at level 0, x constr at level 0).
      Notation "'VType' τ"
        := (CTType τ)
             (in custom p4constructortype at level 0,
                 τ custom p4type).
      Notation "'ControlType' cps ps"
        := (CTControl cps ps)
             (in custom p4constructortype at level 0).
      Notation "'ParserType' cps ps"
        := (CTParser cps ps)
             (in custom p4constructortype at level 0).
      Notation "'PackageType' cps"
        := (CTPackage cps)
             (in custom p4constructortype at level 0).
      Notation "'Extern' cps { mthds }"
        := (CTExtern cps mthds)
             (in custom p4constructortype at level 0).
    End TypeNotations.

    Inductive uop : Set :=
    | Not        (* boolean negation *)
    | BitNot     (* bitwise negation *)
    | UMinus     (* integer negation *)
    | IsValid    (* check header validity *)
    | SetValid   (* set a header valid *)
    | SetInValid (* set a header invalid *)
    | NextIndex  (* get element at [nextIndex] from a header stack *)
    | Size       (* get a header stack's size *)
    | Push (n : positive) (* "push_front," shift stack right by [n] *)
    | Pop  (n : positive) (* "push_front," shift stack left by [n] *).
    (**[]*)

    Module UopNotations.
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
      Notation "'Push' n" := (Push n) (in custom p4uop at level 0).
      Notation "'Pop' n" := (Pop n) (in custom p4uop at level 0).
    End UopNotations.

    (** Binary operations.
        The "Sat" suffix denotes
        saturating arithmetic:
        where there is no overflow. *)
    Inductive bop : Set :=
    | Plus     (* integer addition *)
    | PlusSat  (* saturating addition *)
    | Minus    (* integer subtraction *)
    | MinusSat (* saturating subtraction *)
    | Times    (* multiplication *)
    | Shl      (* bitwise left-shift *)
    | Shr      (* bitwise right-shift *)
    | Le       (* integer less-than *)
    | Ge       (* integer greater-than *)
    | Lt       (* integer less-than or equals *)
    | Gt       (* integer greater-than or equals *)
    | Eq       (* expression equality *)
    | NotEq    (* expression inequality *)
    | BitAnd   (* bitwise and *)
    | BitXor   (* bitwise exclusive-or *)
    | BitOr    (* bitwise or *)
    | PlusPlus (* bit-string concatenation *)
    | And      (* boolean and *)
    | Or       (* boolean or *).
    (**[]*)

    Module BopNotations.
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

    (** Default matchkinds. *)
    Inductive matchkind : Set :=
    | MKExact
    | MKTernary
    | MKLpm.
    (**[]*)

    Instance MatchKindEqDec : EqDec matchkind eq.
    Proof.
      unfold EqDec; unfold equiv, complement.
      intros [] []; try (left; reflexivity);
        try (right; intros H; inversion H).
    Defined.

    Module MatchkindNotations.
      Notation "'M{' x '}M'" := x (x custom p4matchkind at level 99).
      Notation "( x )" := x (in custom p4matchkind, x at level 99).
      Notation "x" := x (in custom p4matchkind at level 0, x constr at level 0).
      Notation "'exact'" := MKExact (in custom p4matchkind at level 0).
      Notation "'ternary'" := MKTernary (in custom p4matchkind at level 0).
      Notation "'lpm'" := MKLpm (in custom p4matchkind at level 0).
    End MatchkindNotations.

    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                     (* booleans *)
      | EBit (width : positive) (val : Z) (i : tags_t) (* unsigned integers *)
      | EInt (width : positive) (val : Z) (i : tags_t) (* signed integers *)
      | EVar (type : t) (x : string)
             (i : tags_t)                              (* variables *)
      | ESlice (n : e) (τ : t)
               (hi lo : positive) (i : tags_t) (* bit-slicing *)
      | ECast (type : t) (arg : e) (i : tags_t) (* explicit casts *)
      | EUop (op : uop) (type : t)
             (arg : e) (i : tags_t)                    (* unary operations *)
      | EBop (op : bop) (lhs_type rhs_type : t)
             (lhs rhs : e) (i : tags_t)                (* binary operations *)
      | ETuple (es : list e) (i : tags_t)              (* tuples *)
      | EStruct (fields : F.fs string (t * e))
                (i : tags_t)                           (* structs and structs *)
      | EHeader (fields : F.fs string (t * e))
                (valid : e) (i : tags_t)               (* header literals *)
      | EExprMember (mem : string)
                    (expr_type : t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : option string)
               (i : tags_t)                            (* error literals *)
      | EMatchKind (mk : matchkind) (i : tags_t)       (* matchkind literals *)
      | EHeaderStack (fields : F.fs string t)
                     (headers : list e) (size : positive)
                     (next_index : Z) (i : tags_t)     (* header stack literals,
                                                          unique to p4light *)
      | EHeaderStackAccess (stack : e) (index : Z)
                           (i : tags_t)                (* header stack indexing *).
      (**[]*)


      
      (** Function call arguments. *)
      Definition args : Type :=
        F.fs string (paramarg (t * e) (t * e)).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type :=
        arrow string (t * e) (t * e) (t * e).
      (**[]*)

      (** Constructor arguments. *)
      Inductive constructor_arg : Type :=
      | CAExpr (expr : e) (* plain expression *)
      | CAName (x : string) (* name of parser, control, package, or extern *).
      (**[]*)

      

      Definition constructor_args : Type := F.fs string constructor_arg.
    End Expressions.

    Arguments EBool {tags_t}.
    Arguments EBit {_}.
    Arguments EInt {_}.
    Arguments EVar {tags_t}.
    Arguments ESlice {_}.
    Arguments ECast {_}.
    Arguments EUop {tags_t}.
    Arguments EBop {tags_t}.
    Arguments ETuple {_}.
    Arguments EStruct {tags_t}.
    Arguments EHeader {_}.
    Arguments EExprMember {tags_t}.
    Arguments EError {tags_t}.
    Arguments EMatchKind {tags_t}.
    Arguments EHeaderStack {_}.
    Arguments EHeaderStackAccess {_}.
    Arguments CAExpr {_}.
    Arguments CAName {_}.

    Module ExprNotations.
      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'TRUE' @ i" := (EBool true i) (in custom p4expr at level 0).
      Notation "'FALSE' @ i" := (EBool false i) (in custom p4expr at level 0).
      Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
      Notation "w 'W' n @ i" := (EBit w n i) (in custom p4expr at level 0).
      Notation "w 'S' n @ i" := (EInt w n i) (in custom p4expr at level 0).
      Notation "'Var' x : ty @ i" := (EVar ty x i)
                            (in custom p4expr at level 0, no associativity).
      Notation "'Slice' n : τ [ hi : lo ] @ i"
               := (ESlice n τ hi lo i)
                    (in custom p4expr at level 10, τ custom p4type,
                        n custom p4expr, right associativity).
      Notation "'Cast' e : τ @ i"
        := (ECast τ e i)
             (in custom p4expr at level 10, τ custom p4type,
                 e custom p4expr, right associativity).
      Notation "'UOP' op x : ty @ i"
               := (EUop op ty x i)
                    (in custom p4expr at level 2,
                        x custom p4expr, ty custom p4type,
                        op custom p4uop, no associativity).
      Notation "'BOP' x : tx op y : ty @ i"
               := (EBop op tx ty x y i)
                    (in custom p4expr at level 10,
                        x custom p4expr, tx custom p4type,
                        y custom p4expr, ty custom p4type,
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
      Notation "'Mem' x : ty 'dot' y @ i"
              := (EExprMember y ty x i)
                    (in custom p4expr at level 10, x custom p4expr,
                        ty custom p4type, left associativity).
      Notation "'Error' x @ i" := (EError x i)
                              (in custom p4expr at level 0, no associativity).
      Notation "'Matchkind' mk @ i" := (EMatchKind mk i)
                              (in custom p4expr at level 0,
                                  mk custom p4matchkind, no associativity).
      Notation "'Stack' hdrs : ts [ n ] 'nextIndex' ':=' ni @ i"
               := (EHeaderStack ts hdrs n ni i)
                    (in custom p4expr at level 0).
      Notation "'Access' e1 [ e2 ] @ i"
               := (EHeaderStackAccess e1 e2 i)
                    (in custom p4expr at level 10, e1 custom p4expr).
    End ExprNotations.
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Module E := Expr.

    Section Statements.
      Variable (tags_t : Type).

      Inductive s : Type :=
      | SSkip (i : tags_t)                              (* skip, useful for
                                                           small-step semantics *)
      | SVardecl (type : E.t)
                 (x : string) (i : tags_t)       (* Variable declaration. *)
      | SAssign (type : E.t) (lhs rhs : E.e tags_t)
                (i : tags_t)                            (* assignment *)
      | SConditional (guard_type : E.t)
                     (guard : E.e tags_t)
                     (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
      | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences *)
      | SBlock (blk : s)                                (* blocks *)
      | SExternMethodCall (e : string) (f : string)
                          (args : E.arrowE tags_t)
                          (i : tags_t)                  (* extern method calls *)
      | SFunCall (f : string)
                 (args : E.arrowE tags_t) (i : tags_t)  (* function call *)
      | SActCall (f : string)
                 (args : E.args tags_t) (i : tags_t)    (* action call *)
      | SReturnVoid (i : tags_t)                        (* void return statement *)
      | SReturnFruit (t : E.t)
                     (e : E.e tags_t)(i : tags_t)       (* fruitful return statement *)
      | SExit (i : tags_t)                              (* exit statement *)
      | SInvoke (x : string) (i : tags_t)          (* table invocation *)
      | SApply (x : string)
               (args : E.args tags_t) (i : tags_t)      (* control apply statements,
                                                           where [x] is the
                                                           name of an instance *).
    (**[]*)
    End Statements.

    Arguments SSkip {tags_t}.
    Arguments SVardecl {_}.
    Arguments SAssign {tags_t}.
    Arguments SConditional {tags_t}.
    Arguments SSeq {tags_t}.
    Arguments SBlock {_}.
    Arguments SFunCall {_}.
    Arguments SActCall {_}.
    Arguments SExternMethodCall {_}.
    Arguments SReturnVoid {tags_t}.
    Arguments SReturnFruit {tags_t}.
    Arguments SExit {_}.
    Arguments SApply {_}.
    Arguments SInvoke {_}.

    Module StmtNotations.
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
      Notation "'var' x : t @ i"
               := (SVardecl t x i)
                    (in custom p4stmt at level 0, t custom p4type).
      Notation "'asgn' e1 ':=' e2 : t @ i"
              := (SAssign t e1 e2 i)
                    (in custom p4stmt at level 40,
                        e1 custom p4expr, e2 custom p4expr,
                        t custom p4type, no associativity).
      Notation "'if' e : t 'then' s1 'else' s2 @ i"
              := (SConditional t e s1 s2 i)
                    (in custom p4stmt at level 80,
                        t custom p4type, e custom p4expr,
                        s1 custom p4stmt, s2 custom p4stmt,
                        no associativity).
      Notation "'call' f 'with' args @ i"
        := (SFunCall f (Arrow args None) i)
             (in custom p4stmt at level 0, no associativity).
      Notation "'let' e : t ':=' 'call' f 'with' args @ i"
               := (SFunCall f (Arrow args (Some (t,e))) i)
                    (in custom p4stmt at level 0,
                        e custom p4expr, t custom p4stmt, no associativity).
      Notation "'funcall' f 'with' args 'into' o @ i"
               := (SFunCall f (Arrow args o) i)
                    (in custom p4stmt at level 0, no associativity).
      Notation "'calling' a 'with' args @ i"
               := (SActCall a args i) (in custom p4stmt at level 0).
      Notation "'extern' e 'calls' f 'with' args 'gives' x @ i"
               := (SExternMethodCall e f (Arrow args x) i)
                    (in custom p4stmt at level 0, no associativity).
      Notation "'return' e : t @ i"
               := (SReturnFruit t e i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4type, no associativity).
      Notation "'returns' @ i"
               := (SReturnVoid i)
                    (in custom p4stmt at level 0, no associativity).
      Notation "'exit' @ i"
               := (SExit i) (in custom p4stmt at level 0, no associativity).
      Notation "'apply' x 'with' args @ i"
               := (SApply x args i) (in custom p4stmt at level 0, no associativity).
      Notation "'invoke' tbl @ i"
               := (SInvoke tbl i) (in custom p4stmt at level 0).
    End StmtNotations.
  End Stmt.

  (** * Parsers *)
  Module Parser.
    Module E := Expr.
    Module S := Stmt.

    Inductive state : Set :=
    | STStart | STAccept | STReject | STName (st : string).
    (**[]*)

    (** Select expression pattern.
        Corresponds to keySet expressions in p4. *)
    Inductive pat : Type :=
    | PATWild
    | PATMask (p1 p2 : pat)
    | PATRange (p1 p2 : pat)
    | PATBit (w : positive) (n : Z)
    | PATInt (w : positive) (n : Z)
    | PATTuple (ps : list pat).
    (**[]*)

    Section Parsers.
      Variable (tags_t : Type).

      (** Parser expressions, which evaluate to state names *)
      Inductive e : Type :=
      | PGoto (st : state) (i : tags_t) (* goto state [st] *)
      | PSelect (exp : E.e tags_t) (default : e)
                (cases : F.fs pat e)
                (i : tags_t)        (* select expressions,
                                       where "default" is
                                       the wild card case *).
      (**[]*)

      (** Parser State Blocks. *)
      Inductive state_block : Type :=
      | State (stmt : S.s tags_t) (transition : e).
      (**[]*)
    End Parsers.

    Arguments PGoto {_}.
    Arguments PSelect {_}.
    Arguments State {_}.

    Module ParserNotations.
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
        := (State s pe)
             (in custom p4prsrstateblock at level 0,
                 s custom p4stmt, pe custom p4prsrexpr).
    End ParserNotations.
  End Parser.

  (** * Controls *)
  Module Control.
    Module E := Expr.
    Module S := Stmt.

    Module ControlDecl.
      Section ControlDecls.
        Variable (tags_t : Type).

        (** Table. *)
        Inductive table : Type :=
        | Table (key : list (E.t * E.e tags_t * E.matchkind))
                (actions : list string).
        (**[]*)

        (** Declarations that may occur within Controls. *)
        (* TODO, this is a stub. *)
        Inductive d : Type :=
        | CDAction (a : string)
                   (signature : E.params)
                   (body : S.s tags_t) (i : tags_t) (* action declaration *)
        | CDTable (t : string) (bdy : table)
                  (i : tags_t)                      (* table declaration *)
        | CDSeq (d1 d2 : d) (i : tags_t).
        (**[]*)
      End ControlDecls.

      Arguments Table {_}.
      Arguments CDAction {_}.
      Arguments CDTable {_}.
      Arguments CDSeq {_}.

      Module ControlDeclNotations.
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
          := (CDTable t (Table ems acts) i)
               (in custom p4ctrldecl at level 0).
      End ControlDeclNotations.
    End ControlDecl.
  End Control.

  (** * Top-Level Declarations *)
  Module TopDecl.
    Module E := Expr.
    Module S := Stmt.
    Module C := Control.ControlDecl.
    Module P := Parser.

    Section TopDeclarations.
      Variable (tags_t : Type).

      (** Top-level declarations. *)
      Inductive d : Type :=
      | TPInstantiate (C : string) (x : string)
                     (cargs : E.constructor_args tags_t)
                     (i : tags_t) (* constructor [C]
                                     with constructor [args]
                                     makes instance [x]. *)
      | TPExtern (e : string)
                 (cparams : E.constructor_params)
                 (methods : F.fs string E.arrowT)
                 (i : tags_t) (* extern declarations *)
      | TPControl (c : string)
                  (cparams : E.constructor_params) (* constructor params *)
                  (params : E.params) (* apply block params *)
                  (body : C.d tags_t) (apply_blk : S.s tags_t) (i : tags_t)
      | TPParser (p : string)
                 (cparams : E.constructor_params) (* constructor params *)
                 (params : E.params)           (* invocation params *)
                 (start : P.state_block tags_t) (* start state *)
                 (states : F.fs string (P.state_block tags_t)) (* parser states *)
                 (i : tags_t) (* parser declaration *)
      | TPFunction (f : string) (signature : E.arrowT) (body : S.s tags_t)
                   (i : tags_t) (* function/method declaration *)
      | TPPackage (p : string)
                  (cparams : E.constructor_params) (* constructor params *)
                  (i : tags_t) (* package type declaration *)
      | TPSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End TopDeclarations.

    Arguments TPInstantiate {_}.
    Arguments TPExtern {_}.
    Arguments TPControl {_}.
    Arguments TPParser {_}.
    Arguments TPFunction {_}.
    Arguments TPPackage {_}.
    Arguments TPSeq {_}.

    Module TopDeclNotations.
      Notation "'%{' decl '}%'" := decl (decl custom p4topdecl at level 99).
      Notation "( x )" := x (in custom p4topdecl, x at level 99).
      Notation "x"
        := x (in custom p4topdecl at level 0, x constr at level 0).
      Notation "d1 ';%;' d2 @ i"
        := (TPSeq d1 d2 i)
             (in custom p4topdecl at level 10,
                 d1 custom p4topdecl, d2 custom p4topdecl,
                 right associativity).
      Notation "'Instance' x 'of' c ( args ) @ i"
        := (TPInstantiate c x args i) (in custom p4topdecl at level 0).
      Notation "'void' f ( params ) { body } @ i"
        := (TPFunction f (Arrow params None) body i)
             (in custom p4topdecl at level 0, body custom p4stmt).
      Notation "'fn' f ( params ) '->' t { body } @ i"
        := (TPFunction f (Arrow params (Some t)) body i)
             (in custom p4topdecl at level 0,
                 t custom p4type, body custom p4stmt).
      Notation "'extern' e ( cparams ) { methods } @ i"
        := (TPExtern e cparams methods i)
             (in custom p4topdecl at level 0).
      Notation "'control' c ( cparams ) ( params ) 'apply' { blk } 'where' { body } @ i"
        := (TPControl c cparams params body blk i)
             (in custom p4topdecl at level 0,
                 blk custom p4stmt, body custom p4ctrldecl).
      Notation "'parser' p ( cparams ) ( params ) 'start' ':=' st { states } @ i"
        := (TPParser p cparams params st states i)
             (in custom p4topdecl at level 0, st custom p4prsrstateblock).
      Notation "'package' p ( cparams ) @ i"
        := (TPPackage p cparams i)
             (in custom p4topdecl at level 0).
    End TopDeclNotations.
  End TopDecl.

  Module P4cubNotations.
    Export Expr.TypeNotations.
    Export Expr.UopNotations.
    Export Expr.BopNotations.
    Export Expr.MatchkindNotations.
    Export Expr.ExprNotations.
    Export Stmt.StmtNotations.
    Export Parser.ParserNotations.
    Export Control.ControlDecl.ControlDeclNotations.
    Export TopDecl.TopDeclNotations.
  End P4cubNotations.
End P4cub.
