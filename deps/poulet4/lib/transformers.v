Require Import Petr4.Syntax.
Require Import Petr4.Typed.
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

Definition N_to_string (n: N): string := to_N_aux (N.to_nat n) n EmptyString.

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  Definition N_to_tempvar (n: N): P4String :=
    P4String.Build_t _ default_tag ("t'" ++ (N_to_string n))%string.

  Eval vm_compute in (N_to_tempvar 1234).

  Fixpoint extractFunCall_ept (nameIdx: N) (exp: @ExpressionPreT tags_t)
           (tag: tags_t) (typ: @P4Type tags_t) (dir: direction):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | ExpBool b => (nil, MkExpression tag (ExpBool b) typ dir, nameIdx)
    | ExpInt i => (nil, MkExpression tag (ExpInt i) typ dir, nameIdx)
    | ExpString str => (nil, MkExpression tag (ExpString str) typ dir, nameIdx)
    | ExpName name => (nil, MkExpression tag (ExpName name) typ dir, nameIdx)
    | ExpArrayAccess array index =>
      let (l1e1, n1) := extractFunCall_exp nameIdx array in
      let (l2e2, n2) := extractFunCall_exp n1 index in
      let (l1, e1) := l1e1 in let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpArrayAccess e1 e2) typ dir, n2)
    | ExpBitStringAccess bits lo hi =>
      let (l1e1, n1) := extractFunCall_exp nameIdx bits in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpBitStringAccess e1 lo hi)
                                                typ dir, n1)
    | ExpList value =>
      let (l1e1, n1) :=
          ((fix extractFunCall_list (idx: N) (l: list (@Expression tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@Expression tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | exp :: rest =>
                let (l2e2, n2) := extractFunCall_exp idx exp in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := extractFunCall_list n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
              end) nameIdx value) in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpList e1) typ dir, n1)
    | ExpRecord entries =>
      let (l1e1, n1) :=
          ((fix extractFunCall_lkv (idx: N) (l: list (@KeyValue tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@KeyValue tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | kv :: rest =>
                let (l2e2, n2) := extractFunCall_keyvalue idx kv in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := extractFunCall_lkv n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
              end) nameIdx entries) in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpRecord e1) typ dir, n1)
    | ExpUnaryOp op arg =>
      let (l1e1, n1) := extractFunCall_exp nameIdx arg in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpUnaryOp op e1) typ dir, n1)
    | ExpBinaryOp op (arg1, arg2) =>
      let (l1e1, n1) := extractFunCall_exp nameIdx arg1 in
      let (l2e2, n2) := extractFunCall_exp n1 arg2 in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpBinaryOp op (e1, e2)) typ dir, n2)
    | ExpCast typ' expr =>
      let (l1e1, n1) := extractFunCall_exp nameIdx expr in
      let (l1, e1) := l1e1 in (l1, MkExpression tag (ExpCast typ' e1) typ dir, n1)
    | ExpTypeMember typ' name =>
      (nil, MkExpression tag (ExpTypeMember typ' name) typ dir, nameIdx)
    | ExpErrorMember mem =>
      (nil, MkExpression tag (ExpErrorMember mem) typ dir, nameIdx)
    | ExpExpressionMember expr name =>
      let (l1e1, n1) := extractFunCall_exp nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1, MkExpression tag (ExpExpressionMember e1 name) typ dir, n1)
    | ExpTernary cond tru fls =>
      let (l1e1, n1) := extractFunCall_exp nameIdx cond in
      let (l2e2, n2) := extractFunCall_exp n1 tru in
      let (l3e3, n3) := extractFunCall_exp n2 fls in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      let (l3, e3) := l3e3 in
      (l1 ++ l2 ++ l3, MkExpression tag (ExpTernary e1 e2 e3) typ dir, n3)
    | ExpFunctionCall func type_args args =>
      let (l1e1, n1) :=
          ((fix extractFunCall_lopt (idx: N) (l: list (option (@Expression tags_t))):
              (list (P4String * (@Expression tags_t)) *
               (list (option (@Expression tags_t))) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | None :: rest =>
                let (l2e2, n2) := extractFunCall_lopt idx rest in
                let (l2, e2) := l2e2 in (l2, None :: e2, n2)
              | Some exp :: rest =>
                let (l2e2, n2) := extractFunCall_exp idx exp in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := extractFunCall_lopt n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, Some e2 :: el3, n3)
              end) nameIdx args) in
      let (l1, e1) := l1e1 in
      (l1 ++ [(N_to_tempvar n1,
               MkExpression tag (ExpFunctionCall func type_args e1) typ dir)],
       MkExpression tag (ExpName (BareName (N_to_tempvar n1))) typ dir, n1 + 1)
    | ExpNamelessInstantiation typ' args =>
      let (l1e1, n1) :=
          ((fix extractFunCall_list (idx: N) (l: list (@Expression tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@Expression tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | exp :: rest =>
                let (l2e2, n2) := extractFunCall_exp idx exp in
                let (l2, e2) := l2e2 in
                let (l3e3, n3) := extractFunCall_list n2 rest in
                let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
              end) nameIdx args) in
      let (l1, e1) := l1e1 in
      (l1, MkExpression tag (ExpNamelessInstantiation typ' e1) typ dir, n1)
    | ExpDontCare => (nil, MkExpression tag ExpDontCare typ dir, nameIdx)
    | ExpMask expr mask =>
      let (l1e1, n1) := extractFunCall_exp nameIdx expr in
      let (l2e2, n2) := extractFunCall_exp n1 mask in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpMask e1 e2) typ dir, n2)
    | ExpRange lo hi =>
      let (l1e1, n1) := extractFunCall_exp nameIdx lo in
      let (l2e2, n2) := extractFunCall_exp n1 hi in
      let (l1, e1) := l1e1 in
      let (l2, e2) := l2e2 in
      (l1 ++ l2, MkExpression tag (ExpRange e1 e2) typ dir, n2)
    end
  with
  extractFunCall_exp (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression tag expr typ dir => extractFunCall_ept nameIdx expr tag typ dir
    end
  with extractFunCall_keyvalue (nameIdx: N) (kv: @KeyValue tags_t):
         (list (P4String * (@Expression tags_t)) * (@KeyValue tags_t) * N) :=
         match kv with
         | MkKeyValue tags key value =>
           let (l1e1, n1) := extractFunCall_exp nameIdx value in
           let (l1, e1) := l1e1 in (l1, MkKeyValue tags key e1, n1)
         end.

  Definition extractFunCall_Expr (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression _ (ExpFunctionCall _ _ _) _ _ => (nil, exp, nameIdx)
    | _ => extractFunCall_exp nameIdx exp
    end.

  Definition to_Statement (tags: tags_t) (typ: StmType)
             (ne: (P4String * (@Expression tags_t))): (@Statement tags_t) :=
    match ne with
    | (name, MkExpression tag expr typ' dir) =>
      MkStatement tags
                  (StatVariable typ' name
                                (Some (MkExpression tag expr typ' dir))) typ
    end.

  Definition to_StmtList (tags: tags_t) (typ: StmType)
             (nel: list (P4String * (@Expression tags_t))): list (@Statement tags_t) :=
    map (to_Statement tags typ) nel.

  Fixpoint extractFunCall_list (idx: N) (l: list (@Expression tags_t)):
    (list (P4String * (@Expression tags_t)) * (list (@Expression tags_t)) * N) :=
    match l with
    | nil => (nil, nil, idx)
    | exp :: rest =>
      let (l2e2, n2) := extractFunCall_exp idx exp in
      let (l2, e2) := l2e2 in
      let (l3e3, n3) := extractFunCall_list n2 rest in
      let (l3, el3) := l3e3 in (l2 ++ l3, e2 :: el3, n3)
    end.

  Fixpoint prepend_to_block (l: list (@Statement tags_t)) (blk: @Block tags_t) :=
    match l with
    | nil => blk
    | x :: rest => BlockCons x (prepend_to_block rest blk)
    end.

  Definition extractFunCall_exp_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let (l1e1, n1) := extractFunCall_exp nameIdx exp in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition extractFunCall_Expr_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let (l1e1, n1) := extractFunCall_Expr nameIdx exp in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition extractFunCall_list_stmt (nameIdx: N) (l: list (@Expression tags_t)):
    (list (@Statement tags_t) * list (@Expression tags_t) * N) :=
      let (l1e1, n1) := extractFunCall_list nameIdx l in
      let (l1, e1) := l1e1 in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Fixpoint extractFunCall_stmtpt (nameIdx: N) (tags: tags_t)
           (stmt: @StatementPreT tags_t) (typ: StmType):
    (list (@Statement tags_t) * N) :=
    match stmt with
    | StatMethodCall _ _ _ => ([MkStatement tags stmt typ], nameIdx)
    | StatAssignment lhs rhs =>
      let (l1e1, n1) := extractFunCall_exp_stmt nameIdx lhs in
      let (l1, e1) := l1e1 in
      let (l2e2, n2) := extractFunCall_Expr_stmt n1 rhs in
      let (l2, e2) := l2e2 in
      (l1 ++ l2 ++ [MkStatement tags (StatAssignment e1 e2) typ], n2)
    | StatDirectApplication typ' args =>
      let (l1e1, n1) := extractFunCall_list_stmt nameIdx args in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatDirectApplication typ' e1) typ], n1)
    | StatConditional cond tru fls =>
      let (l1e1, n1) := extractFunCall_exp_stmt nameIdx cond in
      let (l1, e1) := l1e1 in
      let (stl2, n2) := extractFunCall_stmt n1 tru in
      let (stl3, n3) := match fls with
                        | None => (nil, n2)
                        | Some stmt' => extractFunCall_stmt n2 stmt'
                        end in (l1 ++ stl2 ++ stl3, n3)
    | StatBlock block =>
      let (blk, n1) := extractFunCall_blk nameIdx block in
      ([MkStatement tags (StatBlock blk) typ], n1)
    | StatExit => ([MkStatement tags StatExit typ], nameIdx)
    | StatEmpty => ([MkStatement tags StatEmpty typ], nameIdx)
    | StatReturn None => ([MkStatement tags (StatReturn None) typ], nameIdx)
    | StatReturn (Some expr) =>
      let (l1e1, n1) := extractFunCall_exp_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatReturn (Some e1)) typ], n1)
    | StatSwitch expr cases =>
      let (l1e1, n1) := extractFunCall_exp_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      let (caseList, n2) :=
          ((fix extractFunCall_lssc (idx: N)
                (cs: list (@StatementSwitchCase tags_t)):
              (list (@StatementSwitchCase tags_t) * N) :=
              match cs with
              | nil => (nil, idx)
              | x :: rest =>
                let (c1, n3) := extractFunCall_ssc idx x in
                let (rest', n4) := extractFunCall_lssc n3 rest in (c1 :: rest', n4)
              end) n1 cases) in
      (l1 ++ [MkStatement tags (StatSwitch e1 caseList) typ], n2)
    | StatConstant _ _ _ => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable _ _ None => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable typ' name (Some expr) =>
      let (l1e1, n1) := extractFunCall_Expr_stmt nameIdx expr in
      let (l1, e1) := l1e1 in
      (l1 ++ [MkStatement tags (StatVariable typ' name (Some e1)) typ], n1)
    | StatInstantiation typ' args name init =>
      let (l1e1, n1) := extractFunCall_list_stmt nameIdx args in
      let (l1, e1) := l1e1 in
      let (optBlk, n2) := match init with
                          | None => (None, n1)
                          | Some blk =>
                            let (blk', n3) := extractFunCall_blk n1 blk in
                            (Some blk', n3)
                          end in
      (l1 ++ [MkStatement tags (StatInstantiation typ' e1 name optBlk) typ], n2)
    end
  with extractFunCall_stmt (nameIdx: N) (stmt: @Statement tags_t):
         (list (@Statement tags_t) * N):=
         match stmt with
         | MkStatement tags stmt typ => extractFunCall_stmtpt nameIdx tags stmt typ
         end
  with extractFunCall_blk (nameIdx: N) (blk: @Block tags_t): (@Block tags_t * N) :=
         match blk with
         | BlockEmpty tag => (BlockEmpty tag, nameIdx)
         | BlockCons stmt blk' =>
           let (stl1, n1) := extractFunCall_stmt nameIdx stmt in
           let (blk2, n2) := extractFunCall_blk n1 blk' in
           (prepend_to_block stl1 blk2, n2)
         end
  with extractFunCall_ssc (nameIdx: N) (ssc: @StatementSwitchCase tags_t):
         (@StatementSwitchCase tags_t * N) :=
         match ssc with
         | StatSwCaseAction tags label code =>
           let (blk, n1) := extractFunCall_blk nameIdx code in
           (StatSwCaseAction tags label blk, n1)
         | StatSwCaseFallThrough _ _ => (ssc, nameIdx)
         end.

End Transformer.
