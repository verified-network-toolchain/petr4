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

Definition to_N (n: N): string := to_N_aux (N.to_nat n) n EmptyString.

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  Definition N_to_str (n: N): P4String :=
    P4String.Build_t _ default_tag ("temp" ++ (to_N n))%string.

  Eval vm_compute in (N_to_str 1234).

  Fixpoint extractFunCall_ept (nameIdx: N) (exp: @ExpressionPreT tags_t)
           (tag: tags_t) (typ: @P4Type tags_t) (dir: direction):
    (list (N * (@Expression tags_t)) * (@Expression tags_t) * N) :=
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
              (list (N * (@Expression tags_t)) * (list (@Expression tags_t)) * N) :=
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
              (list (N * (@Expression tags_t)) * (list (@KeyValue tags_t)) * N) :=
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
              (list (N * (@Expression tags_t)) *
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
      (l1 ++ [(n1, MkExpression tag (ExpFunctionCall func type_args e1) typ dir)],
       MkExpression tag (ExpName (BareName (N_to_str n1))) typ dir, n1 + 1)
    | ExpNamelessInstantiation typ' args =>
      let (l1e1, n1) :=
          ((fix extractFunCall_list (idx: N) (l: list (@Expression tags_t)):
              (list (N * (@Expression tags_t)) * (list (@Expression tags_t)) * N) :=
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
    (list (N * (@Expression tags_t)) * (@Expression tags_t) * N) :=
    match exp with
    | MkExpression tag expr typ dir => extractFunCall_ept nameIdx expr tag typ dir
    end
  with
  extractFunCall_keyvalue (nameIdx: N) (kv: @KeyValue tags_t):
    (list (N * (@Expression tags_t)) * (@KeyValue tags_t) * N) :=
    match kv with
    | MkKeyValue tags key value =>
      let (l1e1, n1) := extractFunCall_exp nameIdx value in
      let (l1, e1) := l1e1 in (l1, MkKeyValue tags key e1, n1)
    end.

End Transformer.
