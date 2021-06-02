Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.

Require Import Poulet4.AList.
Require Poulet4.P4String.
Require Poulet4.P4Int.
Require Export Poulet4.Typed.
Require Export Poulet4.Syntax.
Require Export Poulet4.P4cub.Syntax.AST.
Import P4cub.P4cubNotations.

Require Import Coq.Strings.String.
Require Import Coq.Classes.EquivDec.

Require Import Poulet4.Monads.Error.

(** * P4light -> P4cub *)

(* General Unresolved Challenges:
   - What to do about [Locator]?
     Should p4cub use it?
   - How should parametric
     polymorphism be translated?
   - Should there be fresh string generation,
     & if so, how to implement it? *)

Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.

Section Metamorphosis.
  Context {tags_t : Type}.

  (* Error type for fine-grained translation errors *)
  Inductive MorphError :=
    | Inconceivable (msg: string)
    | UnsupportedTy (ty: @P4Type tags_t)
    | UnsupportedExpr (e: @Expression tags_t)
    | UnsupportedStmt (s: @Statement tags_t)
    | UnsupportedBop (o: OpBin).

  (** Type Metamorphosis.
      QUESTIONS:
      - Why do controls & functions have both
        constructors in P4Type and their own
        singleton types?
      - What to do about parametric polymorphism?
      - How exactly will types for
        controls, functions, parsers, actions, tables, & externs be
        translated? How will they be mapped to
        p4cub's constructor types?
      - How, when, & where will [TInteger] be casted?
      - Should &, if so, how will
        header unions, strings, enums, varbits, & sets be compiled?
      - Why is there both a record and a struct type? *)
  Fixpoint type_morph (t : P4Type) : @error_monad MorphError E.t :=
    let fix lrec (ts : list P4Type) : @error_monad MorphError (list E.t) :=
        match ts with
        | []     => mret []
        | t :: ts => t <- type_morph t ;;
                   ts <- lrec ts ;;
                   mret (t :: ts)
        end in
    let fix frec (fs : P4String.AList tags_t P4Type) : @error_monad MorphError (F.fs string E.t) :=
        match fs with
        | []         => mret []
        | (x,t) :: fs => t <- type_morph t ;;
                       fs <- frec fs ;;
                       mret ((P4String.str x, t) :: fs)
        end in
    match t with
    | TypBool => mret {{ Bool }}
    | TypInteger => err (UnsupportedTy t) (* TODO *)
    | TypString => err (UnsupportedTy t) (* TODO *)
    | TypInt w => mret $ E.TInt $ Pos.of_nat w
    | TypBit w => mret $ E.TBit $ Pos.of_nat w
    | TypVarBit _ => err (UnsupportedTy t) (* TODO *)
    | TypArray t n =>
      let n := Pos.of_nat n in
      t' <- type_morph t ;;
      match t' with
      | {{ hdr { ts } }} => mret {{ stack ts[n] }}
      | _ => err (UnsupportedTy t)
      end
    | TypTuple ts
    | TypList  ts => ts <<| lrec ts ;; {{ tuple ts }}
    | TypRecord fs
    | TypStruct fs => fs <<| frec fs ;; {{ rec { fs } }}
    | TypSet t' => type_morph t' (* TODO this is a hack that works for well-behaved parsers, but not in general *)
    | TypError => mret {{ error }}
    | TypMatchKind => mret {{ matchkind }}
    | TypVoid => err (UnsupportedTy t) (* TODO *)
    | TypHeader fs => fs <<| frec fs ;; {{ hdr { fs } }}
    | TypHeaderUnion _ => err (UnsupportedTy t) (* TODO *)
    | TypEnum _ _ _ => err (UnsupportedTy t) (* TODO *)
    | TypTypeName _ => err (UnsupportedTy t) (* TODO *)
    | TypNewType _ t => type_morph t
    | TypControl _ => err (UnsupportedTy t) (* TODO *)
    | TypParser _  => err (UnsupportedTy t) (* TODO *)
    | TypExtern _  => err (UnsupportedTy t) (* TODO *)
    | TypFunction _ => err (UnsupportedTy t) (* TODO *)
    | TypAction _ _ => err (UnsupportedTy t) (* TODO *)
    | TypTable _ => err (UnsupportedTy t) (* TODO *)
    | TypPackage _ _ _ => err (UnsupportedTy t) (* TODO *)
    | TypSpecializedType _ _ => err (UnsupportedTy t) (* TODO, type subsitution? *)
    | TypConstructor _ _ _ _ => err (UnsupportedTy t) (* TODO, type subsitution? *)
    end.
  (**[]*)

  (** Unary Operations *)
  Definition uop_morph (op : OpUni) : E.uop :=
    match op with
    | Not => E.Not
    | BitNot => E.BitNot
    | UMinus => E.UMinus
    end.
  (**[]*)

  (** Binary Operations. *)
  Definition bop_morph (op : OpBin) : @error_monad MorphError E.bop :=
    match op with
    | Plus => mret E.Plus
    | PlusSat => mret E.PlusSat
    | Minus => mret E.Minus
    | MinusSat => mret E.MinusSat
    | Mul => mret E.Times
    | Div => err (UnsupportedBop op)
    | Mod => err (UnsupportedBop op)
    | Shl => mret E.Shl
    | Shr => mret E.Shr
    | Le => mret E.Le
    | Ge => mret E.Ge
    | Lt => mret E.Lt
    | Gt => mret E.Gt
    | Eq => mret E.Eq
    | NotEq => mret E.NotEq
    | BitAnd => mret E.BitAnd
    | BitXor => mret E.BitXor
    | BitOr => mret E.BitOr
    | PlusPlus => mret E.PlusPlus
    | And => mret E.And
    | Or => mret E.Or
    end.
  (**[]*)

  (** Expression Metamorphosis.
      Questions:
      1. How to translate expressions for:
         - integers?
         - strings?
         - type members [ExpTypemember]?
         - ternary expressions?
         - function calls?
         - nameless instantiations?
         - don't care expressions?
         - masks?
         - ranges?
      2. Is [P4Name.t] now redundant by [Locator]?
      3. How to translate [Locator]s?
      4. Should p4cub's header stack accesses
         be restricted to compile-time-known indices?
         From 8.17 "Operations on header stacks",
         "Some implementations may impose the constraint that the
          index expression evaluates to a compile-time known value.
          A P4 compiler must give an error if an index value that is
          a compile-time constant is out of range".
          Otherwise progress needs more assumptions.
      5. Why is [N] still used in [Syntax.v]?
         Didn't we decide it was undesirable to
         use both [N] and [Z]? *)
  Fixpoint expr_morph (e : Expression) : @error_monad MorphError (E.e tags_t) :=
    let fix lrec (es : list Expression) : @error_monad MorphError (list (E.e tags_t)) :=
        match es with
        | []     => mret []
        | e :: es => e <- expr_morph e ;;
                   es <<| lrec es ;; e :: es
        end in
    let fix frec (fs : list KeyValue) : @error_monad MorphError (F.fs string (E.t * E.e tags_t)) :=
        match fs with
        | [] => mret []
        | (MkKeyValue _ x ((MkExpression _ _ t _) as e))
            :: fs => t <- type_morph t ;;
                   e <- expr_morph e ;;
                   fs <<| frec fs ;;
                   (P4String.str x, (t, e)) :: fs
        end in
    match e with
    | MkExpression i (ExpBool b) _ _ => mret <{ BOOL b @ i }>
    | MkExpression i (ExpInt n)  _ _
      => let z := P4Int.value n in
        match P4Int.width_signed n with
        | Some (w, false) => let w := Pos.of_nat w in mret <{ w W z @ i }>
        | Some (w, true)  => let w := Pos.of_nat w in mret <{ w S z @ i }>
        | None => err (UnsupportedExpr e)
        end
    | MkExpression i (ExpName (BareName x) _) t _
      => t <<| type_morph t ;;
        E.EVar t (P4String.str x) i
    | MkExpression i (ExpArrayAccess e1 e2) _ _
      => e1 <- expr_morph e1 ;;
        e2' <- expr_morph e2 ;;
        match e2' with
        | <{ _ W idx @ _ }> => mret <{ Access e1[idx] @ i }>
        | _ => err $ UnsupportedExpr e2 (* TODO *)
        end
    | MkExpression i (ExpBitStringAccess e lo hi) t _
      => let lo := Pos.pred $ N.succ_pos lo in
        let hi := Pos.pred $ N.succ_pos hi in
        t <- type_morph t ;;
        e <<| expr_morph e ;; <{ Slice e:t [hi:lo] @ i }>
    | MkExpression i (ExpList es) _ _
      => es <<| lrec es ;; <{ tup es @ i }>
    | MkExpression i (ExpRecord fs) _ _
      => fs <<| frec fs ;; <{ rec { fs } @ i }>
    | MkExpression i (ExpUnaryOp op e) t _
      => t <- type_morph t ;;
        e <<| expr_morph e ;;
        E.EUop (uop_morph op) t e i
    | MkExpression
        i (ExpBinaryOp
             op ((MkExpression _ _ t1 _) as e1, (MkExpression _ _ t2 _) as e2))
        _ _ => op <- bop_morph op ;;
              t1 <- type_morph t1 ;;
              t2 <- type_morph t2 ;;
              e1 <- expr_morph e1 ;;
              e2 <<| expr_morph e2 ;; <{ BOP e1:t1 op e2:t2 @ i }>
    | MkExpression i (ExpCast t e) _ _
      => t <- type_morph t ;;
        e <<| expr_morph e ;; <{ Cast e:t @ i }>
    | MkExpression i (ExpErrorMember err) _ _
      => mret $ E.EError (mret $ P4String.str err) i
    | MkExpression i (ExpExpressionMember e f) t _ 
      => 
        let f := P4String.str f in 
        t <- type_morph t ;;
        e <<| expr_morph e ;; 
        <{ Mem e:t dot f @ i }>
    | _ => err (UnsupportedExpr e)
    end.
  (**[]*)

  Definition type_expr_morph (e : Expression) : @error_monad MorphError (E.t * E.e tags_t) :=
    match e with
    | MkExpression i _ t _ => t <- type_morph t ;;
                             e <<| expr_morph e ;; (t, e)
    end.
  (**[]*)

  Open Scope string_scope.
  (** Statement Metamorphosis.
      Questions:
      1. How should p4cub deal with constants?
         Should p4cub have constatnts?
      2. How to translate:
         - blocks? Should p4cub have blocks?
         - direct applications?
           The name of the control being applied
           is not in [Syntax.v] nor [Typed.v]?
         - method calls? Type subsitution?
      3. How to get parameter names to generate arguments?
      4. When and how will instantiations be lifted? *)
  Fixpoint stmt_morph (s : Statement) : @error_monad MorphError (ST.s tags_t) :=
    let fix blk_morph (blk : Block) : @error_monad MorphError (ST.s tags_t) :=
        match blk with
        | BlockEmpty i => mret -{ skip @ i }-
        | BlockCons ((MkStatement i _ _) as s) blk
          => s1 <- stmt_morph s ;;
            s2 <<| blk_morph blk ;; -{ s1; s2 @ i }-
        end in
    (* let fix switch_case_morph (swcase : StatementSwitchCase) : option (ST.s tags_t) :=
        match swcase with
        end in *)
    match s with
    | MkStatement i StatEmpty _ => mret -{ skip @ i }-
    | MkStatement i StatExit  _ => mret -{ exit @ i }-
    | MkStatement i (StatReturn None) _ => mret -{ returns @ i }-
    | MkStatement
        i (StatReturn (Some ((MkExpression _ _ t _) as e))) _
      => t <- type_morph t ;;
        e <<| expr_morph e ;; -{ return e:t @ i }-
    | MkStatement i (StatVariable t x None _) _
      => t <<| type_morph t ;;
        let x := P4String.str x in -{ var x:t @ i }-
    | MkStatement i (StatVariable t x (Some e) _) _
      => t <- type_morph t ;;
        e <<| expr_morph e ;;
        let x := P4String.str x in
        -{ var x:t @ i; asgn Var x:t @ i := e:t @ i @ i }-
    | MkStatement i (StatAssignment e1 ((MkExpression _ _ t _) as e2)) _
      => t <- type_morph t ;;
        e1 <- expr_morph e1 ;;
        e2 <<| expr_morph e2 ;; -{ asgn e1 := e2:t @ i }-
    | MkStatement i (StatBlock blk) _ => s <<| blk_morph blk ;; -{ b{ s }b }-
    | MkStatement i (StatConditional ((MkExpression _ _ t _) as e) s1 None) _
      => t <- type_morph t ;;
        e <- expr_morph e ;;
        s1 <<| stmt_morph s1 ;;
        -{ if e:t then s1 else skip @ i @ i }-
    | MkStatement i (StatConditional ((MkExpression _ _ t _) as e) s1 (Some s2)) _
      => t <- type_morph t ;;
        e <- expr_morph e ;;
        s1 <- stmt_morph s1 ;;
        s2 <<| stmt_morph s2 ;;
        -{ if e:t then s1 else s2 @ i }-
    | MkStatement
        i (StatMethodCall
             (MkExpression _ 
                (ExpExpressionMember 
                  (MkExpression _ 
                    (ExpName (BareName x) _) 
                    (TypTypeName (BareName xty)) 
                    _)
                  fname)
                (TypFunction (MkFunctionType _ _ FunExtern retty))
                _)
              _
              args)
        _
      =>
        let x := P4String.str x in 
        let xty := P4String.str xty in 
        let fname := P4String.str fname in 
        if xty == "packet_in" 
        then
          args' <- 
            match args with 
            | Some e :: nil => 
              let* '(t, e') := type_expr_morph e in
              mret (("arg", P4cub.PAOut (t, e')) :: nil)
            | _ => mret nil
            end ;;
          ty' <- mret None ;;
          mret -{ extern x calls fname with args' gives ty' @ i }-
        else err (UnsupportedStmt s)
    | MkStatement i (StatSwitch e cases) _
      => e <- expr_morph e ;; err (UnsupportedStmt s) (* TODO *)
    | MkStatement _ _ _ => err (UnsupportedStmt s)
    end.
  (**[]*)

  Definition parser_case_morph 
    (c: @ParserCase tags_t) 
    : @error_monad MorphError (P.Parser.pat * string) :=
    let 'MkParserCase tag matches next := c in 
    let combine_pats := fun (p: list P.Parser.pat) =>
      match p with 
      | pat :: nil => mret pat
      | _ :: _ => mret [{ PTUP p }]
      | nil => err $ Inconceivable "missing pattern base case"
      end in
    let match_worker (m: Match) := 
      let 'MkMatch tag m' ty := m in 
      match m' with 
      | MatchDontCare => mret [{ ?? }]
      | MatchExpression me => 
        e' <- expr_morph me ;; 
        match e' with 
        | <{ w W n @ _ }> => mret [{ w PW n }]
        | <{ w S n @ _ }> => mret [{ w PS n }]
        | _ => err $ UnsupportedExpr me
        end
      end in 
    pats <- sequence (map match_worker matches) ;;
    pats' <- combine_pats pats ;;
    mret (pats', P4String.str next).


  Definition morph_str (n: string) := 
    match n with 
    | "start" => ={ start }=
    | "accept" => ={ accept }=
    | "reject" => ={ reject }=
    | name => ={ δ name }=
    end.

    Definition morph_name (n: P4String.t tags_t) := morph_str (P4String.str n).

  Fixpoint get_default 
    (tag: tags_t) 
    (cases: list (P.Parser.pat * string)) 
    : @error_monad MorphError (P.Parser.e tags_t) :=
    match cases with 
    | nil => err $ Inconceivable "missing default case in parser select"
    | ([{ ?? }], s) :: _ => 
      let st := morph_str s in 
      mret p{ goto st @ tag }p
    | _ :: cases => get_default tag cases
    end.

  Definition morph_cexpr 
    (tag: tags_t)
    (x: P.Parser.pat * string) 
    : P.Parser.pat * (P.Parser.e tags_t) := 
    let '(pat, nxt) := x in 
    let st := morph_str nxt in 
    let nxt_jump := p{ goto st @ tag }p in 
    (pat, nxt_jump). 

  Definition parser_trans_morph
    (t: @ParserTransition tags_t)
    : @error_monad MorphError (P.Parser.e tags_t) :=
    match t with 
    | ParserDirect tag next_name => 
      let st := morph_name next_name in 
      mret p{ goto st @ tag }p
    | ParserSelect tag es cases =>
      cub_cases <- sequence (map parser_case_morph cases) ;; 
      cub_exprs <- sequence (map expr_morph es) ;;
      def <- get_default tag cub_cases ;;
      let exp := E.ETuple cub_exprs tag in 
      let cub_cases' := map (fun '(k, v) => let v' := morph_str v in (k, p{ goto v' @ tag }p)) cub_cases in 
      mret p{ select exp { cub_cases' } default := def @ tag }p
    end.

  Fixpoint combine_ss (tag: tags_t) (ss: list (ST.s tags_t)) : ST.s tags_t := 
    match ss with 
    | nil => -{ skip @ tag }-
    | s :: ss' => 
      ST.SSeq s (combine_ss tag ss') tag
    end.

  Definition parser_state_morph 
    (ps: @ParserState tags_t) 
    : @error_monad MorphError (string * P.Parser.state_block tags_t) :=
    let 'MkParserState tag name ss trans := ps in 
    ss' <- sequence (map stmt_morph ss) ;; 
    trans' <- parser_trans_morph trans ;; 
    mret (P4String.str name, P.Parser.State (combine_ss tag ss') trans').

End Metamorphosis.
