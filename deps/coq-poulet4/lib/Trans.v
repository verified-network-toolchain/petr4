Require Import Syntax.
Require Import Typed.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Import Coq.Lists.List.ListNotations.

Open Scope N_scope.

Definition to_digit (n: N): ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.

Fixpoint to_N_aux (time: nat) (n: N) (acc: string): string :=
  let (ndiv10, nmod10) := N.div_eucl n 10 in
  let acc' := String (to_digit nmod10) acc in
  match time with
  | O => acc'
  | S time' => match ndiv10 with
               | 0 => acc'
               | n' => to_N_aux time' n' acc'
               end
  end.

Definition N_to_string (n: N): string := to_N_aux (N.to_nat (N.log2 n)) n EmptyString.

Definition add1 (n: N): N := n + 1.

Definition Nzero: N := 0.

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  Definition N_to_tempvar (n: N): P4String :=
    P4String.Build_t _ default_tag ("t'" ++ (N_to_string n))%string.

  Eval vm_compute in (N_to_tempvar 123412341234).

  Fixpoint transform_ept (nameIdx: N) (exp: @ExpressionPreT tags_t)
           (tag: tags_t) (typ: @P4Type tags_t) (dir: direction):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | ExpBool b => (nil, MkExpression tag (ExpBool b) typ dir, nameIdx)
    | ExpInt i => (nil, MkExpression tag (ExpInt i) typ dir, nameIdx)
    | ExpString str => (nil, MkExpression tag (ExpString str) typ dir, nameIdx)
    | ExpName name => (nil, MkExpression tag (ExpName name) typ dir, nameIdx)
    | ExpArrayAccess array index =>
      let (l1e1, n1) := transform_exp nameIdx array in
      let (l2e2, n2) := transform_exp n1 index in
      let (l1, e1) := l1e1 in let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpArrayAccess e1 e2) typ dir, n2)
    | ExpBitStringAccess bits lo hi =>
      let (l1e1, n1) := transform_exp nameIdx bits in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpBitStringAccess e1 lo hi)
                                                typ dir, n1)
    | ExpList value =>
      let (l1e1, n1) :=
          ((fix transform_list (idx: N) (l: list (@Expression tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@Expression tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | exp :: rest =>
                let (l2e2, n2) := transform_exp idx exp in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := transform_list n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
              end) nameIdx value) in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpList e1) typ dir, n1)
    | ExpRecord entries =>
      let (l1e1, n1) :=
          ((fix transform_lkv (idx: N) (l: list (@KeyValue tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@KeyValue tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | kv :: rest =>
                let (l2e2, n2) := transform_keyvalue idx kv in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := transform_lkv n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
              end) nameIdx entries) in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpRecord e1) typ dir, n1)
    | ExpUnaryOp op arg =>
      let (l1e1, n1) := transform_exp nameIdx arg in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpUnaryOp op e1) typ dir, n1)
    | ExpBinaryOp op (arg1, arg2) =>
      let (l1e1, n1) := transform_exp nameIdx arg1 in
      let (l2e2, n2) := transform_exp n1 arg2 in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpBinaryOp op (e1, e2)) typ dir, n2)
    | ExpCast typ' expr =>
      let (l1e1, n1) := transform_exp nameIdx expr in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpCast typ' e1) typ dir, n1)
    | ExpTypeMember typ' name =>
      (nil, MkExpression tag (ExpTypeMember typ' name) typ dir, nameIdx)
    | ExpErrorMember mem =>
      (nil, MkExpression tag (ExpErrorMember mem) typ dir, nameIdx)
    | ExpExpressionMember expr name =>
      let (l1e1, n1) := transform_exp nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1, MkExpression tag (ExpExpressionMember e1 name) typ dir, n1)
    | ExpTernary cond tru fls =>
      let (l1e1, n1) := transform_exp nameIdx cond in
      let (l2e2, n2) := transform_exp n1 tru in
      let (l3e3, n3) := transform_exp n2 fls in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      let (l3, e3) := l3e3 in
      (l1 ++ l2 ++ l3, MkExpression tag (ExpTernary e1 e2 e3) typ dir, n3)
    | ExpFunctionCall func type_args args =>
      let (l1e1, n1) :=
          ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))):
              (list (P4String * (@Expression tags_t)) *
               (list (option (@Expression tags_t))) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | None :: rest =>
                let (l2e2, n2) := transform_lopt idx rest in
                let (l2, e2) := l2e2 in (l2, None :: e2, n2)
              | Some exp :: rest =>
                let (l2e2, n2) := transform_exp idx exp in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := transform_lopt n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, Some e2 :: el3, n3)
              end) nameIdx args) in
      let (l1, e1) := l1e1 in
      (l1 ++ [(N_to_tempvar n1,
               MkExpression tag (ExpFunctionCall func type_args e1) typ dir)],
       MkExpression tag (ExpName (BareName (N_to_tempvar n1))) typ dir, add1 n1)
    | ExpNamelessInstantiation typ' args =>
      ([(N_to_tempvar nameIdx,
               MkExpression tag (ExpNamelessInstantiation typ' args) typ dir)],
       MkExpression tag (ExpName (BareName (N_to_tempvar nameIdx))) typ dir, add1 nameIdx)
    | ExpDontCare => (nil, MkExpression tag ExpDontCare typ dir, nameIdx)
    | ExpMask expr mask =>
      let (l1e1, n1) := transform_exp nameIdx expr in
      let (l2e2, n2) := transform_exp n1 mask in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpMask e1 e2) typ dir, n2)
    | ExpRange lo hi =>
      let (l1e1, n1) := transform_exp nameIdx lo in
      let (l2e2, n2) := transform_exp n1 hi in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpRange e1 e2) typ dir, n2)
    end
  with
  transform_exp (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression tag expr typ dir => transform_ept nameIdx expr tag typ dir
    end
  with transform_keyvalue (nameIdx: N) (kv: @KeyValue tags_t):
         (list (P4String * (@Expression tags_t)) * (@KeyValue tags_t) * N) :=
         match kv with
         | MkKeyValue tags key value =>
           let (l1e1, n1) := transform_exp nameIdx value in
           let (l1, e1) := l1e1 in (l1, MkKeyValue tags key e1, n1)
         end.

  Definition transform_Expr (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression _ (ExpFunctionCall _ _ _) _ _ => (nil, exp, nameIdx)
    | _ => transform_exp nameIdx exp
    end.

  Definition expr_to_stmt (tags: tags_t) (typ: StmType)
             (ne: (P4String * (@Expression tags_t))): (@Statement tags_t) :=
    match ne with
    | (name, MkExpression tag expr typ' dir) =>
      match expr with
      | ExpNamelessInstantiation typ'' e1 =>
        MkStatement tags (StatInstantiation typ'' e1 name None) typ
      | _ => MkStatement tags
                         (StatVariable typ' name
                                       (Some (MkExpression tag expr typ' dir))) typ
      end
    end.

  Definition to_StmtList (tags: tags_t) (typ: StmType)
             (nel: list (P4String * (@Expression tags_t))): list (@Statement tags_t) :=
    map (expr_to_stmt tags typ) nel.

  Fixpoint transform_list {A B C: Type} (f: N -> A -> (list B * C * N))
           (idx: N) (l: list A): (list B * list C * N) :=
    match l with
    | nil => (nil, nil, idx)
    | exp :: rest =>
      let (l2e2, n2) := f idx exp in
      let (l2, e2) := l2e2 in
      let (l3e3, n3) := transform_list f n2 rest in
      let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
    end.

  Definition transform_exprs (idx: N) (l: list (@Expression tags_t)):
    (list (P4String * (@Expression tags_t)) * (list (@Expression tags_t)) * N) :=
    transform_list transform_exp idx l.

  Fixpoint prepend_to_block (l: list (@Statement tags_t)) (blk: @Block tags_t) :=
    match l with
    | nil => blk
    | x :: rest => BlockCons x (prepend_to_block rest blk)
    end.

  Definition transform_exp_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let (l1e1, n1) := transform_exp nameIdx exp in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition transform_Expr_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let (l1e1, n1) := transform_Expr nameIdx exp in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition transform_list_stmt (nameIdx: N) (l: list (@Expression tags_t)):
    (list (@Statement tags_t) * list (@Expression tags_t) * N) :=
      let (l1e1, n1) := transform_exprs nameIdx l in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Fixpoint transform_stmtpt (nameIdx: N) (tags: tags_t)
           (stmt: @StatementPreT tags_t) (typ: StmType):
    (list (@Statement tags_t) * N) :=
    match stmt with
    | StatMethodCall _ _ _ => ([MkStatement tags stmt typ], nameIdx)
    | StatAssignment lhs rhs =>
      let (l1e1, n1) := transform_exp_stmt nameIdx lhs in
      let (l1, e1) := l1e1 in
      let (l2e2, n2) := transform_Expr_stmt n1 rhs in
      let (l2, e2) := l2e2 in
      (l1 ++ l2 ++ [MkStatement tags (StatAssignment e1 e2) typ], n2)
    | StatDirectApplication typ' args =>
      let (l1e1, n1) := transform_list_stmt nameIdx args in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatDirectApplication typ' e1) typ], n1)
    | StatConditional cond tru fls =>
      let (l1e1, n1) := transform_exp_stmt nameIdx cond in
      let (l1, e1) := l1e1 in
      let (stl2, n2) := transform_stmt n1 tru in
      let (stl3, n3) := match fls with
                        | None => (nil, n2)
                        | Some stmt' => transform_stmt n2 stmt'
                        end in (l1 ++ stl2 ++ stl3, n3)
    | StatBlock block =>
      let (blk, n1) := transform_blk nameIdx block in
      ([MkStatement tags (StatBlock blk) typ], n1)
    | StatExit => ([MkStatement tags StatExit typ], nameIdx)
    | StatEmpty => ([MkStatement tags StatEmpty typ], nameIdx)
    | StatReturn None => ([MkStatement tags (StatReturn None) typ], nameIdx)
    | StatReturn (Some expr) =>
      let (l1e1, n1) := transform_exp_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatReturn (Some e1)) typ], n1)
    | StatSwitch expr cases =>
      let (l1e1, n1) := transform_exp_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      let (caseList, n2) :=
          ((fix transform_lssc (idx: N)
                (cs: list (@StatementSwitchCase tags_t)):
              (list (@StatementSwitchCase tags_t) * N) :=
              match cs with
              | nil => (nil, idx)
              | x :: rest =>
                let (c1, n3) := transform_ssc idx x in
                let (rest', n4) := transform_lssc n3 rest in (c1 :: rest', n4)
              end) n1 cases) in
      (l1 ++ [MkStatement tags (StatSwitch e1 caseList) typ], n2)
    | StatConstant _ _ _ => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable _ _ None => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable typ' name (Some expr) =>
      let (l1e1, n1) := transform_Expr_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatVariable typ' name (Some e1)) typ], n1)
    | StatInstantiation typ' args name init => ([MkStatement tags stmt typ], nameIdx)
    end
  with transform_stmt (nameIdx: N) (stmt: @Statement tags_t):
         (list (@Statement tags_t) * N):=
         match stmt with
         | MkStatement tags stmt typ => transform_stmtpt nameIdx tags stmt typ
         end
  with transform_blk (nameIdx: N) (blk: @Block tags_t): (@Block tags_t * N) :=
         match blk with
         | BlockEmpty tag => (BlockEmpty tag, nameIdx)
         | BlockCons stmt blk' =>
           let (stl1, n1) := transform_stmt nameIdx stmt in
           let (blk2, n2) := transform_blk n1 blk' in
           (prepend_to_block stl1 blk2, n2)
         end
  with transform_ssc (nameIdx: N) (ssc: @StatementSwitchCase tags_t):
         (@StatementSwitchCase tags_t * N) :=
         match ssc with
         | StatSwCaseAction tags label code =>
           let (blk, n1) := transform_blk nameIdx code in
           (StatSwCaseAction tags label blk, n1)
         | StatSwCaseFallThrough _ _ => (ssc, nameIdx)
         end.

  Definition expr_to_decl (ne: P4String * (@Expression tags_t)):
    (@Declaration tags_t) :=
    match ne with
    | (name, MkExpression tags expr typ dir) =>
      match expr with
      | ExpNamelessInstantiation typ' args =>
        DeclInstantiation tags  typ' args name None
      | _ => DeclVariable default_tag typ name (Some (MkExpression tags expr typ dir))
      end
    end.

  Fixpoint transform_list' {A: Type} (f: N -> A -> (list A * N))
           (nameIdx: N) (l: list A): (list A * N) :=
    match l with
    | nil => (nil, nameIdx)
    | x :: rest =>
      let (l1, n1) := f nameIdx x in
      let (l2, n2) := transform_list' f n1 rest in (l1 ++ l2, n2)
    end.

  Definition transform_match (nameIdx: N) (mt: @Match tags_t):
    (list (@Declaration tags_t) * (@Match tags_t) * N) :=
    match mt with
    | MkMatch tags expr typ =>
      match expr with
      | MatchDontCare => (nil, mt, nameIdx)
      | MatchExpression exp =>
        let (l1e1, n1) := transform_exp nameIdx exp in
        let (l1, e1) := l1e1 in
        (map expr_to_decl l1, MkMatch tags (MatchExpression e1) typ, n1)
      end
    end.

  Definition transform_psrcase (nameIdx: N) (pc: @ParserCase tags_t):
    (list (@Declaration tags_t) * (@ParserCase tags_t) * N) :=
    match pc with
    | MkParserCase tags matches next =>
      let (l1m1, n1) := transform_list transform_match nameIdx matches in
      let (l1, m1) := l1m1 in
      (l1, MkParserCase tags m1 next, n1)
    end.

  Definition transform_psrtrans (nameIdx: N) (pt: @ParserTransition tags_t):
    (list (@Declaration tags_t) * (@ParserTransition tags_t) * N) :=
    match pt with
    | ParserDirect _ _ => (nil, pt, nameIdx)
    | ParserSelect tags exprs cases =>
      let (l1e1, n1) := transform_exprs nameIdx exprs in
      let (l1, e1) := l1e1 in
      let (l2c2, n2) := transform_list transform_psrcase n1 cases in
      let (l2, c2) := l2c2 in
      (map expr_to_decl l1 ++ l2, ParserSelect tags e1 c2, n2)
    end.

  Definition transform_psrst (nameIdx: N) (ps: @ParserState tags_t):
    (list (@Declaration tags_t) * (@ParserState tags_t) * N) :=
    match ps with
    | MkParserState tags name statements transition =>
      let (l1, n1) := transform_list' transform_stmt nameIdx statements in
      let (l2t2, n2) := transform_psrtrans n1 transition in
      let (l2, t2) := l2t2 in (l2, MkParserState tags name l1 t2, n2)
    end.

  Definition transform_tblkey (nameIdx: N) (tk: @TableKey tags_t):
    (list (@Declaration tags_t) * (@TableKey tags_t) * N) :=
    match tk with
    | MkTableKey tags key match_kind =>
      let (l1e1, n1) := transform_exp nameIdx key in
      let (l1, e1) := l1e1 in (map expr_to_decl l1, MkTableKey tags e1 match_kind, n1)
    end.

  Definition transform_opt (nameIdx: N) (opt: option (@Expression tags_t)):
    (list (P4String * (@Expression tags_t)) * (option (@Expression tags_t)) * N) :=
    match opt with
    | None => (nil, None, nameIdx)
    | Some exp =>
      let (l1e1, n1) := transform_exp nameIdx exp in
      let (l1, e1) := l1e1 in (l1, Some e1, n1)
    end.

  Definition transform_tpar (nameIdx: N) (tpar: @TablePreActionRef tags_t):
    (list (@Declaration tags_t) * (@TablePreActionRef tags_t) * N) :=
    match tpar with
    | MkTablePreActionRef name args =>
      let (l1e1, n1) := transform_list transform_opt nameIdx args in
      let (l1, e1) := l1e1 in
      (map expr_to_decl l1, MkTablePreActionRef name e1, n1)
    end.

  Definition transform_tar (nameIdx: N) (tar: @TableActionRef tags_t):
    (list (@Declaration tags_t) * (@TableActionRef tags_t) * N) :=
    match tar with
    | MkTableActionRef tags action typ =>
      let (l1e1, n1) := transform_tpar nameIdx action in
      let (l1, e1) := l1e1 in (l1, MkTableActionRef tags e1 typ, n1)
    end.

  Definition transform_tblenty (nameIdx: N) (te: @TableEntry tags_t):
    (list (@Declaration tags_t) * (@TableEntry tags_t) * N) :=
    match te with
    | MkTableEntry tags matches action =>
      let (l1e1, n1) := transform_list transform_match nameIdx matches in
      let (l1, e1) := l1e1 in
      let (l2e2, n2) := transform_tar n1 action in
      let (l2, e2) := l2e2 in (l1 ++ l2, MkTableEntry tags e1 e2, n2)
    end.

  Definition transform_tblprop (nameIdx: N) (tp: @TableProperty tags_t):
    (list (@Declaration tags_t) * (@TableProperty tags_t) * N) :=
    match tp with
    | MkTableProperty tags const name value =>
      let (l1e1, n1) := transform_exp nameIdx value in
      let (l1, e1) := l1e1 in
      (map expr_to_decl l1, MkTableProperty tags const name e1, n1)
    end.

  Definition transform_membr (nameIdx: N) (ne: (P4String * @Expression tags_t)):
             (list (@Declaration tags_t) * (P4String * @Expression tags_t) * N) :=
    match ne with
    | (n, exp) =>
      let (l1e1, n1) := transform_exp nameIdx exp in
      let (l1, e1) := l1e1 in (map expr_to_decl l1, (n, e1), n1)
    end.

  Definition lastDecl (l: list (@Declaration tags_t)): (@Declaration tags_t) :=
    last l (DeclError default_tag nil).

  Fixpoint transform_decl (nameIdx: N) (decl: @Declaration tags_t):
    (list (@Declaration tags_t) * N) :=
    match decl with
    | DeclConstant _ _ _ _ => ([decl], nameIdx)
    | DeclInstantiation tags typ args name init => ([decl], nameIdx)
    | DeclParser tags name type_params params cparams locals states =>
      let (local', n1) :=
          ((fix transform_decl_list (idx: N) (l: list (@Declaration tags_t)):
              (list (@Declaration tags_t) * N) :=
              match l with
              | nil => (nil, idx)
              | x :: rest =>
                let (l2, n2) := transform_decl idx x in
                let (l3, n3) := transform_decl_list n2 rest in (l2 ++ l3, n3)
              end) nameIdx locals) in
      let (l2s2, n2) := transform_list transform_psrst n1 states in
      let (l2, s2) := l2s2 in
      (local' ++ l2 ++ [DeclParser tags name type_params params cparams local' s2], n1)
    | DeclControl tags name type_params params cparams locals appl =>
      let (local', n1) :=
          ((fix transform_decl_list (idx: N) (l: list (@Declaration tags_t)):
              (list (@Declaration tags_t) * N) :=
              match l with
              | nil => (nil, idx)
              | x :: rest =>
                let (l2, n2) := transform_decl idx x in
                let (l3, n3) := transform_decl_list n2 rest in (l2 ++ l3, n3)
              end) nameIdx locals) in
      let (blk, n2) := transform_blk n1 appl in
      ([DeclControl tags name type_params params cparams local' blk], n2)
    | DeclFunction tags ret name type_params params body =>
      let (blk, n1) := transform_blk nameIdx body in
      ([DeclFunction tags ret name type_params params blk], n1)
    | DeclExternFunction _ _ _ _ _ => ([decl], nameIdx)
    | DeclVariable _ _ _ None => ([decl], nameIdx)
    | DeclVariable tags typ name (Some expr) =>
      let (l1e1, n1) := transform_Expr nameIdx expr in
      let (l1, e1) := l1e1 in
      (map expr_to_decl l1 ++ [DeclVariable tags typ name (Some e1)], n1)
    | DeclValueSet tags typ size name =>
      let (l1e1, n1) := transform_Expr nameIdx size in
      let (l1, e1) := l1e1 in
      (map expr_to_decl l1 ++ [DeclValueSet tags typ e1 name], n1)
    | DeclAction tags name data_params ctrl_params body =>
      let (blk, n1) := transform_blk nameIdx body in
      ([DeclAction tags name data_params ctrl_params blk], n1)
    | DeclTable tags name key actions entries default_action size
                custom_properties =>
      let (l1e1, n1) := transform_list transform_tblkey nameIdx key in
      let (l1, e1) := l1e1 in
      let (l2e2, n2) := transform_list transform_tar n1 actions in
      let (l2, e2) := l2e2 in
      let (l3e3, n3) :=
          (match entries with
           | None => (nil, None, n2)
           | Some ets =>
             let (l4e4, n4) := transform_list transform_tblenty n2 ets in
             let (l4, e4) := l4e4 in (l4, Some e4, n4) end) in
      let (l3, e3) := l3e3 in
      let (l5e5, n5) := (match default_action with
                         | None => (nil, None, n3)
                         | Some da =>
                           let (l6e6, n6) := transform_tar n3 da in
                           let (l6, e6) := l6e6 in (l6, Some e6, n6)
                         end) in
      let(l5, e5) := l5e5 in
      let (l6e6, n6) :=
          transform_list transform_tblprop n5 custom_properties in
      let (l6, e6) := l6e6 in
      (l1 ++ l2 ++ l3 ++ l5 ++ l6 ++ [DeclTable tags name e1 e2 e3 e5 size e6], n6)
    | DeclHeader _ _ _ => ([decl], nameIdx)
    | DeclHeaderUnion _ _ _ => ([decl], nameIdx)
    | DeclStruct _ _ _ => ([decl], nameIdx)
    | DeclError _ _ => ([decl], nameIdx)
    | DeclMatchKind _ _ => ([decl], nameIdx)
    | DeclEnum _ _ _ => ([decl], nameIdx)
    | DeclSerializableEnum tags typ name members =>
      let (l1e1, n1) := transform_list transform_membr nameIdx members in
      let (l1, e1) := l1e1 in (l1 ++ [DeclSerializableEnum tags typ name e1], n1)
    | DeclExternObject _ _ _ _ => ([decl], nameIdx)
    | DeclTypeDef _ _ (inl _) => ([decl], nameIdx)
    | DeclTypeDef tags name (inr decl') =>
      let (l1, n1) := transform_decl nameIdx decl' in
      (removelast l1 ++ [DeclTypeDef tags name (inr (lastDecl l1))], n1)
    | DeclNewType _ _ (inl _) => ([decl], nameIdx)
    | DeclNewType tags name (inr decl') =>
      let (l1, n1) := transform_decl nameIdx decl' in
      (removelast l1 ++ [DeclNewType tags name (inr (lastDecl l1))], n1)
    | DeclControlType _ _ _ _ => ([decl], nameIdx)
    | DeclParserType _ _ _ _ => ([decl], nameIdx)
    | DeclPackageType _ _ _ _ => ([decl], nameIdx)
    end.

  Definition transform_prog (prog: @program tags_t): (@program tags_t) :=
    match prog with
    | Program l =>
      let (l', _) := transform_list' transform_decl Nzero l in Program l'
    end.

End Transformer.
