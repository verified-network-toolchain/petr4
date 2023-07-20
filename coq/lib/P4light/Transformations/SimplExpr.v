
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Typed.

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

Fixpoint N_to_string_aux (time: nat) (n: N) (acc: string): string :=
  let (ndiv10, nmod10) := N.div_eucl n 10 in
  let acc' := String (to_digit nmod10) acc in
  match time with
  | O => acc'
  | S time' => match ndiv10 with
               | 0 => acc'
               | n' => N_to_string_aux time' n' acc'
               end
  end.

Definition N_to_string (n: N): string := N_to_string_aux (N.to_nat (N.log2 n)) n EmptyString.

Definition add1 (n: N): N := n + 1.

Definition Nzero: N := 0.

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  Definition N_to_tempvar (n: N): P4String :=
    P4String.Build_t _ default_tag ("t'" ++ (N_to_string n))%string.

  (* Eval vm_compute in (N_to_tempvar 123412341234).*)
  (* transform_exp turns an expression to a list of statements and a side-effect-free expression. *)
  Fixpoint transform_exp (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression tag expr typ dir => transform_ept nameIdx expr tag typ dir
    end
  with transform_ept (nameIdx: N) (exp: @ExpressionPreT tags_t)
           (tag: tags_t) (typ: @P4Type tags_t) (dir: direction):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | ExpBool b => (nil, MkExpression tag (ExpBool b) typ dir, nameIdx)
    | ExpInt i => (nil, MkExpression tag (ExpInt i) typ dir, nameIdx)
    | ExpString str => (nil, MkExpression tag (ExpString str) typ dir, nameIdx)
    | ExpName name loc => (nil, MkExpression tag (ExpName name loc) typ dir, nameIdx)
    | ExpArrayAccess array index =>
      let '(l1, e1, n1) := transform_exp nameIdx array in
      let '(l2, e2, n2) := transform_exp n1 index in
      (l1 ++ l2, MkExpression tag (ExpArrayAccess e1 e2) typ dir, n2)
    | ExpBitStringAccess bits lo hi =>
      let '(l1, e1, n1) := transform_exp nameIdx bits in
      (l1, MkExpression tag (ExpBitStringAccess e1 lo hi) typ dir, n1)
    | ExpList value =>
      let '(l1, e1, n1) :=
          ((fix transform_list (idx: N) (l: list (@Expression tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (list (@Expression tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | exp :: rest =>
                let '(l2, e2, n2) := transform_exp idx exp in
                let '(l3, e3, n3) := transform_list n2 rest in
                (l2 ++ l3, e2 :: e3, n3)
              end) nameIdx value) in
      (l1, MkExpression tag (ExpList e1) typ dir, n1)
    | ExpRecord entries =>
      let '(l1, e1, n1) :=
          ((fix transform_alist (idx: N) (l: P4String.AList tags_t (@Expression tags_t)):
              (list (P4String * (@Expression tags_t)) *
               (P4String.AList tags_t (@Expression tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | (key, value) :: rest =>
                let '(l2, e2, n2) := transform_exp idx value in
                let '(l3, e3, n3) := transform_alist n2 rest in
                (l2 ++ l3, (key, e2) :: e3, n3)
              end) nameIdx entries) in
      (l1, MkExpression tag (ExpRecord e1) typ dir, n1)
    | ExpUnaryOp op arg =>
      let '(l1, e1, n1) := transform_exp nameIdx arg in
      (l1, MkExpression tag (ExpUnaryOp op e1) typ dir, n1)
    | ExpBinaryOp op arg1 arg2 =>
      let '(l1, e1, n1) := transform_exp nameIdx arg1 in
      let '(l2, e2, n2) := transform_exp n1 arg2 in
      (l1 ++ l2, MkExpression tag (ExpBinaryOp op e1 e2) typ dir, n2)
    | ExpCast typ' expr =>
      let '(l1, e1, n1) := transform_exp nameIdx expr in
      (l1, MkExpression tag (ExpCast typ' e1) typ dir, n1)
    | ExpTypeMember typ' name =>
      (nil, MkExpression tag (ExpTypeMember typ' name) typ dir, nameIdx)
    | ExpErrorMember mem =>
      (nil, MkExpression tag (ExpErrorMember mem) typ dir, nameIdx)
    | ExpExpressionMember expr name =>
      let '(l1, e1, n1) := transform_exp nameIdx expr in
      (l1, MkExpression tag (ExpExpressionMember e1 name) typ dir, n1)
    | ExpTernary cond tru fls =>
      let '(l1, e1, n1) := transform_exp nameIdx cond in
      let '(l2, e2, n2) := transform_exp n1 tru in
      let '(l3, e3, n3) := transform_exp n2 fls in
      (* Qinshi: This is incorrect. l2/l3 is only evaluated when the boolean is true/false. *)
      (l1 ++ l2 ++ l3, MkExpression tag (ExpTernary e1 e2 e3) typ dir, n3)
    (* | ExpFunctionCall (MkExpression tag (ExpExpressionMember expr name) etyp dir) [] [] => *)
    (*   if String.eqb (P4String.str name) "isValid" then *)
    (*     (nil, MkExpression tag (ExpExpressionMember expr name) TypBool dir, nameIdx) *)
    (*   else *)
    (*     (* There are evaluation order issues here, also in bin_op, List, Record, etc. *) *)
    (*     let type_args := [] in *)
    (*     let args := [] in *)
    (*     let '(l0, e0, n0) := *)
    (*         let '(l1, e1, n1) := transform_exp nameIdx expr in *)
    (*         (l1, MkExpression tag (ExpExpressionMember e1 name) typ dir, n1) *)
    (*     in *)
    (*     let '(l1, e1, n1) := *)
    (*         ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))): *)
    (*            (list (P4String * (@Expression tags_t)) * *)
    (*             (list (option (@Expression tags_t))) * N) := *)
    (*             match l with *)
    (*             | nil => (nil, nil, idx) *)
    (*             | None :: rest => *)
    (*               let '(l2, e2, n2) := transform_lopt idx rest in *)
    (*               (l2, None :: e2, n2) *)
    (*             | Some exp :: rest => *)
    (*               let '(l2, e2, n2) := transform_exp idx exp in *)
    (*               let '(l3, e3, n3) := transform_lopt n2 rest in *)
    (*               (l2 ++ l3, Some e2 :: e3, n3) *)
    (*             end) n0 args) in *)
    (*     (l0 ++ l1 ++ [(N_to_tempvar n1, *)
    (*                    MkExpression tag (ExpFunctionCall e0 type_args e1) typ dir)], *)
    (*      MkExpression tag (ExpName (BareName (N_to_tempvar n1)) NoLocator) typ InOut, add1 n1) *)
    | ExpFunctionCall func type_args args =>
      (* There are evaluation order issues here, also in bin_op, List, Record, etc. *)
      let '(l0, e0, n0) := transform_exp nameIdx func in
      let '(l1, e1, n1) :=
        ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))):
              (list (P4String * (@Expression tags_t)) *
               (list (option (@Expression tags_t))) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | None :: rest =>
                let '(l2, e2, n2) := transform_lopt idx rest in
                (l2, None :: e2, n2)
              | Some exp :: rest =>
                let '(l2, e2, n2) := transform_exp idx exp in
                let '(l3, e3, n3) := transform_lopt n2 rest in
                (l2 ++ l3, Some e2 :: e3, n3)
              end) n0 args) in
      (l0 ++ l1 ++ [(N_to_tempvar n1,
               MkExpression tag (ExpFunctionCall e0 type_args e1) typ dir)],
       MkExpression tag (ExpName (BareName (N_to_tempvar n1)) NoLocator) typ InOut, add1 n1)
    | ExpNamelessInstantiation typ' args =>
      (nil, MkExpression tag (ExpNamelessInstantiation typ' args) typ dir, nameIdx)
    | ExpDontCare => (nil, MkExpression tag ExpDontCare typ dir, nameIdx)
    end.

  (* transform_Expr allows top-level function call, comparing with transform_exp. *)
  Definition transform_Expr (nameIdx: N) (exp: @Expression tags_t):
    (list (P4String * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression _ (ExpFunctionCall _ _ _) _ _ =>
      let '(l1, e1, n1) := transform_exp nameIdx exp in
      match l1 with
      | [x] => (nil, exp, nameIdx)
      | _ => (l1, e1, n1)
      end
    | _ => transform_exp nameIdx exp
    end.

  Definition expr_to_stmt (tags: tags_t) (typ: StmType)
             (ne: (P4String * (@Expression tags_t))): (@Statement tags_t) :=
    match ne with
    | (name, MkExpression tag expr typ' dir) =>
      match expr with
      | _ => MkStatement tags
                         (StatVariable typ' name
                                       (Some (MkExpression tag expr typ' dir)) NoLocator) typ
      end
    end.
  Definition expr_to_assign (tags: tags_t) (typ: StmType)
             (ne: (P4String * (@Expression tags_t))): (@Statement tags_t) :=
    match ne with
    | (name, MkExpression tag expr typ' dir) =>
      match expr with
      | _ =>
        let lhs := MkExpression tag (ExpName (BareName name) NoLocator) typ' dir in
        let rhs := MkExpression tag expr typ' dir in
        let stmtpt := StatAssignment lhs rhs in
        MkStatement tags stmtpt typ
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
      let '(l2, e2, n2) := f idx exp in
      let '(l3, e3, n3) := transform_list f n2 rest in
      (l2 ++ l3, e2 :: e3, n3)
    end.

  Definition transform_exprs (idx: N) (l: list (@Expression tags_t)):
    (list (P4String * (@Expression tags_t)) * (list (@Expression tags_t)) * N) :=
    transform_list transform_exp idx l.

  Fixpoint prepend_to_block (l: list (@Statement tags_t)) (blk: @Block tags_t) :=
    match l with
    | nil => blk
    | x :: rest => BlockCons x (prepend_to_block rest blk)
    end.

  Definition stmts_to_block (l : list (@Statement tags_t)) :=
    prepend_to_block l (BlockEmpty default_tag).

  Definition stmts_to_stmt (l : list (@Statement tags_t)) :=
    match l with
    | [stmt] => stmt
    | _ =>
        MkStatement default_tag (StatBlock (stmts_to_block l)) StmUnit
    end.

  Definition transform_exp_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let '(l1, e1, n1) := transform_exp nameIdx exp in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition transform_Expr_stmt (nameIdx: N) (exp: @Expression tags_t):
    (list (@Statement tags_t) * (@Expression tags_t) * N) :=
      let '(l1, e1, n1) := transform_Expr nameIdx exp in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition transform_list_stmt (nameIdx: N) (l: list (@Expression tags_t)):
    (list (@Statement tags_t) * list (@Expression tags_t) * N) :=
      let '(l1, e1, n1) := transform_exprs nameIdx l in
      let stl1 := to_StmtList default_tag StmVoid l1 in (stl1, e1, n1).

  Definition find_table_apply
           (decl_assigns : list (string * list (@Statement tags_t)))
           (func : @Expression tags_t) (args : list (option (@Expression tags_t))) : option (list (@Statement tags_t)) :=
    match args with
    | [] =>
      let '(MkExpression _ func_pe _ _ ) := func in
      match func_pe with
      | ExpExpressionMember (MkExpression _ (ExpName (BareName name) loc) _ _) func_name =>
        if String.eqb (P4String.str func_name) "apply" then
           match List.find (fun '(table_name, _) => String.eqb (P4String.str name) table_name) decl_assigns with
           | Some (_, assigns) => Some assigns
           | None => None
           end
        else None
      | _ =>
      None
      end
    | _ =>
      None
    end.


  Fixpoint transform_stmtpt (decl_assigns : list (string * list (@Statement tags_t))) (nameIdx: N) (tags: tags_t)
           (stmt: @StatementPreT tags_t) (typ: StmType):
    (list (@Statement tags_t) * N) :=
    match stmt with
    | StatMethodCall func type_args args =>
      match find_table_apply decl_assigns func args with
      | Some lk =>
        let '(largs, args, n1) :=
            ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))):
               (list (@Statement tags_t) *
                (list (option (@Expression tags_t))) * N) :=
                match l with
                | nil => (nil, nil, idx)
                | None :: rest =>
                  let '(l2, e2, n2) := transform_lopt idx rest in
                  (l2, None :: e2, n2)
                | Some exp :: rest =>
                  let '(l2, e2, n2) := transform_exp_stmt idx exp in
                  let '(l3, e3, n3) := transform_lopt n2 rest in
                  (l2 ++ l3, Some e2 :: e3, n3)
                end) nameIdx args) in (* does the nameIdx need to change? *)
        (largs ++ lk ++ [MkStatement tags (StatMethodCall func type_args args) typ], n1)
      | None =>
        let '(l0, e0, n0) := transform_exp_stmt nameIdx func in
        let '(l1, e1, n1) :=
            ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))):
               (list (@Statement tags_t) *
                (list (option (@Expression tags_t))) * N) :=
                match l with
                | nil => (nil, nil, idx)
                | None :: rest =>
                  let '(l2, e2, n2) := transform_lopt idx rest in
                  (l2, None :: e2, n2)
                | Some exp :: rest =>
                  let '(l2, e2, n2) := transform_exp_stmt idx exp in
                  let '(l3, e3, n3) := transform_lopt n2 rest in
                  (l2 ++ l3, Some e2 :: e3, n3)
                end) n0 args) in
        (l0 ++ l1 ++ [MkStatement tags (StatMethodCall e0 type_args e1) typ], n1)
      end
    | StatAssignment lhs rhs =>
      let '(l1, e1, n1) := transform_exp_stmt nameIdx lhs in
      let '(l2, e2, n2) := transform_Expr_stmt n1 rhs in
      (l1 ++ l2 ++ [MkStatement tags (StatAssignment e1 e2) typ], n2)
    | StatDirectApplication typ' func_type args =>
      let '(l1, e1, n1) :=
          ((fix transform_lopt (idx: N) (l: list (option (@Expression tags_t))):
              (list (@Statement tags_t) *
               (list (option (@Expression tags_t))) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | None :: rest =>
                let '(l2, e2, n2) := transform_lopt idx rest in
                (l2, None :: e2, n2)
              | Some exp :: rest =>
                let '(l2, e2, n2) := transform_exp_stmt idx exp in
                let '(l3, e3, n3) := transform_lopt n2 rest in
                (l2 ++ l3, Some e2 :: e3, n3)
              end) nameIdx args) in
      (l1 ++ [MkStatement tags (StatDirectApplication typ' func_type e1) typ], n1)
    | StatConditional cond tru fls =>
      let '(l1, e1, n1) := transform_exp_stmt nameIdx cond in
      let (stl2, n2) := transform_stmt decl_assigns n1 tru in
      let (stl3, n3) :=
        match fls with
        | None => (nil, n2)
        | Some stmt' => transform_stmt decl_assigns n2 stmt'
        end in
      (l1 ++ [MkStatement tags (StatConditional e1 (stmts_to_stmt stl2) (Some (stmts_to_stmt stl3))) typ], n3)
    | StatBlock block =>
      let (blk, n1) := transform_blk decl_assigns nameIdx block in
      ([MkStatement tags (StatBlock blk) typ], n1)
    | StatExit => ([MkStatement tags StatExit typ], nameIdx)
    | StatEmpty => ([MkStatement tags StatEmpty typ], nameIdx)
    | StatReturn None => ([MkStatement tags (StatReturn None) typ], nameIdx)
    | StatReturn (Some expr) =>
      let '(l1, e1, n1) := transform_exp_stmt nameIdx expr in
      (l1 ++ [MkStatement tags (StatReturn (Some e1)) typ], n1)
    | StatSwitch expr cases =>
      let '(l1, e1, n1) := transform_exp_stmt nameIdx expr in
      let (caseList, n2) :=
          ((fix transform_lssc (idx: N)
                (cs: list (@StatementSwitchCase tags_t)):
              (list (@StatementSwitchCase tags_t) * N) :=
              match cs with
              | nil => (nil, idx)
              | x :: rest =>
                let (c1, n3) := transform_ssc decl_assigns idx x in
                let (rest', n4) := transform_lssc n3 rest in (c1 :: rest', n4)
              end) n1 cases) in
      (l1 ++ [MkStatement tags (StatSwitch e1 caseList) typ], n2)
    | StatConstant _ _ _ _ => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable _ _ None _ => ([MkStatement tags stmt typ], nameIdx)
    | StatVariable typ' name (Some expr) loc =>
      let '(l1, e1, n1) := transform_Expr_stmt nameIdx expr in
      (l1 ++ [MkStatement tags (StatVariable typ' name (Some e1) loc) typ], n1)
    | StatInstantiation typ' args name init => ([MkStatement tags stmt typ], nameIdx)
    end
  with transform_stmt (decl_assigns : list (string * list (@Statement tags_t)))  (nameIdx: N) (stmt: @Statement tags_t):
         (list (@Statement tags_t) * N):=
         match stmt with
         | MkStatement tags stmt typ => transform_stmtpt decl_assigns nameIdx tags stmt typ
         end
  with transform_blk (decl_assigns : list (string * list (@Statement tags_t))) (nameIdx: N) (blk: @Block tags_t): (@Block tags_t * N) :=
         match blk with
         | BlockEmpty tag => (BlockEmpty tag, nameIdx)
         | BlockCons stmt blk' =>
           let (stl1, n1) := transform_stmt decl_assigns nameIdx stmt in
           let (blk2, n2) := transform_blk decl_assigns n1 blk' in
           (prepend_to_block stl1 blk2, n2)
         end
  with transform_ssc (decl_assigns : list (string * list (@Statement tags_t))) (nameIdx: N) (ssc: @StatementSwitchCase tags_t):
         (@StatementSwitchCase tags_t * N) :=
         match ssc with
         | StatSwCaseAction tags label code =>
           let (blk, n1) := transform_blk decl_assigns nameIdx code in
           (StatSwCaseAction tags label blk, n1)
         | StatSwCaseFallThrough _ _ => (ssc, nameIdx)
         end.

  Definition expr_to_decl (ne: P4String * (@Expression tags_t)):
    (@Declaration tags_t) :=
    match ne with
    | (name, MkExpression tags expr typ dir) =>
       DeclVariable default_tag typ name (Some (MkExpression tags expr typ dir))
    end.

  Definition str_to_decl (ne: P4String * (@Expression tags_t)):
    (@Declaration tags_t) :=
    match ne with
    | (name, MkExpression tags _ typ _) =>
      DeclVariable default_tag typ name None
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
      | MatchMask expr mask =>
        let '(l1, e1, n1) := transform_exp nameIdx expr in
        let '(l2, e2, n2) := transform_exp n1 mask in
        (map expr_to_decl (l1 ++ l2), MkMatch tags (MatchMask e1 e2) typ, n2)
      | MatchRange lo hi =>
        let '(l1, e1, n1) := transform_exp nameIdx lo in
        let '(l2, e2, n2) := transform_exp n1 hi in
        (map expr_to_decl (l1 ++ l2), MkMatch tags (MatchRange e1 e2) typ, n2)
      | MatchCast typ' expr =>
        let '(l1, e1, n1) := transform_exp nameIdx expr in
        (map expr_to_decl l1, MkMatch tags (MatchCast typ' e1) typ, n1)
      end
    end.

  Definition transform_psrcase (nameIdx: N) (pc: @ParserCase tags_t):
    (list (@Declaration tags_t) * (@ParserCase tags_t) * N) :=
    match pc with
    | MkParserCase tags matches next =>
      let '(l1, m1, n1) := transform_list transform_match nameIdx matches in
      (l1, MkParserCase tags m1 next, n1)
    end.

  Definition transform_psrtrans (nameIdx: N) (pt: @ParserTransition tags_t):
    (list (@Declaration tags_t) * (@ParserTransition tags_t) * N) :=
    match pt with
    | ParserDirect _ _ => (nil, pt, nameIdx)
    | ParserSelect tags exprs cases =>
      let '(l1, e1, n1) := transform_exprs nameIdx exprs in
      let '(l2, c2, n2) := transform_list transform_psrcase n1 cases in
      (map expr_to_decl l1 ++ l2, ParserSelect tags e1 c2, n2)
    end.

  Definition transform_psrst (decl_assigns : list (string * list (@Statement tags_t))) (nameIdx: N) (ps: @ParserState tags_t):
    (list (@Declaration tags_t) * (@ParserState tags_t) * N) :=
    match ps with
    | MkParserState tags name statements transition =>
      let (l1, n1) := transform_list' (transform_stmt decl_assigns) nameIdx statements in
      let '(l2, t2, n2) := transform_psrtrans n1 transition in
      (l2, MkParserState tags name l1 t2, n2)
    end.

  Definition transform_tblkey (nameIdx: N) (tk: @TableKey tags_t):
    (list (P4String * @Expression tags_t) * (@TableKey tags_t) * N) :=
    match tk with
    | MkTableKey tags key match_kind =>
      let '(l1, e1, n1) := transform_exp nameIdx key in
      let '(MkExpression _ _ typ _) := key in
      (l1, MkTableKey tags e1 match_kind, n1)
    end.

  Definition transform_opt (nameIdx: N) (opt: option (@Expression tags_t)):
    (list (P4String * (@Expression tags_t)) * (option (@Expression tags_t)) * N) :=
    match opt with
    | None => (nil, None, nameIdx)
    | Some exp =>
      let '(l1, e1, n1) := transform_exp nameIdx exp in
      (l1, Some e1, n1)
    end.

  Definition transform_tpar (nameIdx: N) (tpar: @TablePreActionRef tags_t):
    (list (@Declaration tags_t) * (@TablePreActionRef tags_t) * N) :=
    match tpar with
    | MkTablePreActionRef name args =>
      let '(l1, e1, n1) := transform_list transform_opt nameIdx args in
      (map expr_to_decl l1, MkTablePreActionRef name e1, n1)
    end.

  Definition transform_tar (nameIdx: N) (tar: @TableActionRef tags_t):
    (list (@Declaration tags_t) * (@TableActionRef tags_t) * N) :=
    match tar with
    | MkTableActionRef tags action typ =>
      let '(l1, e1, n1) := transform_tpar nameIdx action in
      (l1, MkTableActionRef tags e1 typ, n1)
    end.

  Definition transform_tblenty (nameIdx: N) (te: @TableEntry tags_t):
    (list (@Declaration tags_t) * (@TableEntry tags_t) * N) :=
    match te with
    | MkTableEntry tags matches action =>
      let '(l1, e1, n1) := transform_list transform_match nameIdx matches in
      let '(l2, e2, n2) := transform_tar n1 action in
      (l1 ++ l2, MkTableEntry tags e1 e2, n2)
    end.

  Definition transform_tblprop (nameIdx: N) (tp: @TableProperty tags_t):
    (list (@Declaration tags_t) * (@TableProperty tags_t) * N) :=
    match tp with
    | MkTableProperty tags const name value =>
      let '(l1, e1, n1) := transform_exp nameIdx value in
      (map expr_to_decl l1, MkTableProperty tags const name e1, n1)
    end.

  Definition transform_membr (nameIdx: N) (ne: (P4String * @Expression tags_t)):
             (list (@Declaration tags_t) * (P4String * @Expression tags_t) * N) :=
    match ne with
    | (n, exp) =>
      let '(l1, e1, n1) := transform_exp nameIdx exp in
      (map expr_to_decl l1, (n, e1), n1)
    end.

  Definition lastDecl (l: list (@Declaration tags_t)): (@Declaration tags_t) :=
    last l (DeclError default_tag nil).

  Fixpoint transform_decl (decl_assigns : list (string * list (@Statement tags_t))) (nameIdx: N) (decl: @Declaration tags_t) :
    (list (@Declaration tags_t) * list (string * list (@Statement tags_t)) * N) :=
    match decl with
    | DeclConstant _ _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclInstantiation tags typ args name init => ([decl], decl_assigns, nameIdx)
    | DeclParser tags name type_params params cparams locals states =>
      let '(local', decl_assigns', n1) :=
          ((fix transform_decl_list (idx: N) (l: list (@Declaration tags_t)):
              (list (@Declaration tags_t) * list (string * list (@Statement tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | x :: rest =>
                let '(l2, decl_assigns2, n2) := transform_decl nil idx x in
                let '(l3, decl_assigns3, n3) := transform_decl_list n2 rest in
                (l2 ++ l3, decl_assigns2 ++ decl_assigns3, n3)
              end) nameIdx locals) in
      let '(l2, s2, n2) := transform_list (transform_psrst decl_assigns) n1 states in
      ([DeclParser tags name type_params params cparams (local' ++ l2) s2],
       decl_assigns ++ decl_assigns',
       n2)
    | DeclControl tags name type_params params cparams locals appl =>
      let '(local', decl_assigns1, n1) :=
          ((fix transform_decl_list (idx: N) (l: list (@Declaration tags_t)):
              (list (@Declaration tags_t) * list (string * list (@Statement tags_t)) * N) :=
              match l with
              | nil => (nil, nil, idx)
              | x :: rest =>
                let '(l2, decl_assigns2, n2) := transform_decl nil idx x in
                let '(l3, decl_assigns3, n3) := transform_decl_list n2 rest in
                (l2 ++ l3, decl_assigns2 ++ decl_assigns3, n3)
              end) nameIdx locals) in
      let decl_assigns2 := decl_assigns1 ++ decl_assigns in
      let '(blk, n2) := transform_blk decl_assigns2 n1 appl in
      ([DeclControl tags name type_params params cparams local' blk],
       decl_assigns2,
       n2)
    | DeclFunction tags ret name type_params params body =>
      let (blk, n1) := transform_blk decl_assigns nameIdx body in
      ([DeclFunction tags ret name type_params params blk], decl_assigns, n1)
    | DeclExternFunction _ _ _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclVariable _ _ _ None => ([decl], decl_assigns, nameIdx)
    | DeclVariable tags typ name (Some expr) =>
      let '(l1, e1, n1) := transform_Expr nameIdx expr in
      (map expr_to_decl l1 ++ [DeclVariable tags typ name (Some e1)],
       decl_assigns,
       n1)
    | DeclValueSet tags typ size name => ([decl], decl_assigns, nameIdx)
    | DeclAction tags name data_params ctrl_params body =>
      let (blk, n1) := transform_blk decl_assigns nameIdx body in
      ([DeclAction tags name data_params ctrl_params blk],
       decl_assigns,
       n1)
    | DeclTable tags name key actions entries default_action size
                custom_properties =>
      let '(l1, e1, n1) := transform_list transform_tblkey nameIdx key in
      let assigns := List.map (expr_to_assign tags StmUnit) l1 in
      let decls := List.map str_to_decl l1 in
      let decl_assigns1 := (P4String.str name, assigns) :: decl_assigns in
      let '(l2, e2, n2) := transform_list transform_tar n1 actions in
      let '(l3, e3, n3) :=
          (match entries with
           | None => (nil, None, n2)
           | Some ets =>
             let '(l4, e4, n4) := transform_list transform_tblenty n2 ets in
             (l4, Some e4, n4) end) in
      let '(l5, e5, n5) := (match default_action with
                         | None => (nil, None, n3)
                         | Some da =>
                           let '(l6, e6, n6) := transform_tar n3 da in
                           (l6, Some e6, n6)
                         end) in
      let '(l6, e6, n6) :=
          transform_list transform_tblprop n5 custom_properties in
      (decls ++ l2 ++ l3 ++ l5 ++ l6 ++ [DeclTable tags name e1 e2 e3 e5 size e6],
       decl_assigns1,
       n6)
    | DeclHeader _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclHeaderUnion _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclStruct _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclError _ _ => ([decl], decl_assigns, nameIdx)
    | DeclMatchKind _ _ => ([decl], decl_assigns, nameIdx)
    | DeclEnum _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclSerializableEnum tags typ name members =>
      (* Qinshi: I don't think we need to transform here, because these expressions should be constant. *)
      let '(l1, e1, n1) := transform_list transform_membr nameIdx members in
      (l1 ++ [DeclSerializableEnum tags typ name e1],
       decl_assigns,
       n1)
    | DeclExternObject _ _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclTypeDef _ _ (inl _) => ([decl], decl_assigns, nameIdx)
    | DeclTypeDef tags name (inr decl') =>
      let '(l1, decl_assigns1, n1) := transform_decl decl_assigns nameIdx decl' in
      (removelast l1 ++ [DeclTypeDef tags name (inr (lastDecl l1))], decl_assigns1, n1)
    | DeclNewType _ _ (inl _) => ([decl], decl_assigns, nameIdx)
    | DeclNewType tags name (inr decl') =>
      let '(l1, decl_assigns1, n1) := transform_decl decl_assigns nameIdx decl' in
      (removelast l1 ++ [DeclNewType tags name (inr (lastDecl l1))], decl_assigns1, n1)
    | DeclControlType _ _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclParserType _ _ _ _ => ([decl], decl_assigns, nameIdx)
    | DeclPackageType _ _ _ _ => ([decl], decl_assigns, nameIdx)
    end.

    Fixpoint transform_list'' {A B: Type} (f: B -> N -> A -> (list A * B * N))
            (decl_assigns : B) (nameIdx: N)(l: list A): (list A * B * N) :=
    match l with
    | nil => (nil, decl_assigns, nameIdx)
    | x :: rest =>
      let '(l1, decl_assigns1, n1) := f decl_assigns nameIdx x in
      let '(l2, decl_assigns2, n2) := transform_list'' f decl_assigns1 n1 rest in
      (l1 ++ l2, decl_assigns2, n2)
    end.


  Definition transform_prog (prog: @program tags_t): (@program tags_t) :=
    match prog with
    | Program l =>
      let '(l', _, _) := transform_list'' transform_decl nil Nzero l in Program l'
    end.

End Transformer.
