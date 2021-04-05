Require Import Syntax.
Require Import Typed.
Require Import SemUtil.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Import Coq.Lists.List.ListNotations.

Open Scope monad.
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

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  Fixpoint summarize_stmtpt (tags: tags_t) (stmt: @StatementPreT tags_t) (typ: StmType):
        (list P4String) :=
    match stmt with
    | StatDirectApplication typ' args => [get_type_name typ']
    | StatBlock block => summarize_blk block
    | StatSwitch expr cases => concat (map summarize_ssc cases)
    | StatInstantiation typ' args name init => [name]
    | _ => nil
    end
  with summarize_stmt (stmt: @Statement tags_t):
      (list P4String) :=
    match stmt with
    | MkStatement tags stmt typ => summarize_stmtpt tags stmt typ
    end
  with summarize_blk (blk: @Block tags_t): (list P4String) :=
    match blk with
    | BlockEmpty tag => nil
    | BlockCons stmt blk' => summarize_stmt stmt ++ summarize_blk blk'
    end
  with summarize_ssc (ssc: @StatementSwitchCase tags_t): (list P4String) :=
    match ssc with
    | StatSwCaseAction tags label code => summarize_blk code
    | StatSwCaseFallThrough _ _ => nil
    end.

  (* Definition summarize_stmts stmts :=
    concat (map summarize_stmt stmts). *)

  Definition summarize_decl (decl: @Declaration tags_t): (list P4String) :=
    match decl with
    | DeclInstantiation tags typ args name init => [name]
    | DeclAction tags name data_params ctrl_params body =>
        summarize_blk body
    | _ => nil
    end.

  (* TODO *)
  Definition summarize_parser (locals: list (@Declaration tags_t)) (states: list (@ParserState tags_t)):
      (list P4String) :=
    nil.

  Definition summarize_control (locals: list (@Declaration tags_t)) (apply: @Block tags_t):
      (list P4String) :=
    concat (map summarize_decl locals) ++ summarize_blk apply.

  Definition state := list P4String.
  Definition exception := unit.
  Definition monad := @state_monad state exception.

  Definition error {T: Type}: monad T := state_fail tt.

  Definition has {T: Type} (eqb: T -> T -> bool) (x: T) (l: list T): bool :=
    existsb (eqb x) l.

  Definition equivb: P4String -> P4String -> bool := @P4String.equivb tags_t.

  Definition is_used (n: P4String): monad bool :=
    let* used_list := get_state in
    mret (has equivb n used_list).

  Definition var_name (n: P4String) (cnt: N): P4String :=
    if cnt =? 0%N then n else
      let str := P4String.str n in P4String.Build_t _ default_tag (str ++ (N_to_string cnt))%string.

  Fixpoint fresh' (n: P4String) (cnt: N) (fuel: nat): monad P4String :=
    match fuel with
    | O => error
    | S fuel =>
        let n' := var_name n cnt in
        let* b := is_used n' in
        if b then fresh' n (cnt+1) fuel else mret n'
    end.

  Definition fresh (n: P4String): monad P4String :=
    let* used_list := get_state in
    let* n' := fresh' n 0 (1 + length used_list)%nat in
    let* _ := put_state (fun l =>n' :: l) in
    mret n'.

  Definition env := @IdentMap.t tags_t (@Locator tags_t).

  Definition name_to_loc (e: env) (n: @Typed.name tags_t) :=
    match n with
    | BareName name =>
        match IdentMap.get name e with
        | Some l => l
        | None => NoLocator
        end
    | QualifiedName path name =>
        LGlobal (path ++ [name])
    end.

  Fixpoint transform_ept (e: env) (tags: tags_t) (expr: @ExpressionPreT tags_t) (typ: P4Type) (dir: direction):
      @Expression tags_t :=
    match expr with
    | _ => MkExpression tags expr typ dir
    end
  with transform_expr (e: env) (expr: @Expression tags_t): @Expression tags_t :=
    match expr with
    | MkExpression tag expr typ dir => transform_ept e tag expr typ dir
    end
  with transform_keyvalue (e: env) (kv: @KeyValue tags_t): @KeyValue tags_t :=
    match kv with
    | MkKeyValue tags key value =>
        MkKeyValue tags key (transform_expr e value)
    end.

  Definition transform_exprs (e: env) (exprs: list (@Expression tags_t)): list (@Expression tags_t) :=
    map (transform_expr e) exprs.

  Definition transform_oexprs (e: env) (oexprs: list (option (@Expression tags_t))):
      list (option (@Expression tags_t)) :=
    let f oexpr :=
      match oexpr with
      | Some expr => Some (transform_expr e expr)
      | None => None
      end in
    map f oexprs.

  Section transform_stmt.
  Variable (LocCons: list P4String -> @Locator tags_t). (* LGlobal or LInstance *)

    Fixpoint transform_stmtpt (e: env) (ns: list P4String) (tags: tags_t) (stmt: @StatementPreT tags_t) (typ: StmType):
        monad (@Statement tags_t * env) :=
      match stmt with
      | StatMethodCall func type_args args =>
        let func' := transform_expr e func in
        let args' := transform_oexprs e args in
        mret (MkStatement tags (StatMethodCall func' type_args args') typ, e)
      | StatAssignment lhs rhs =>
        let lhs' := transform_expr e lhs in
        let rhs' := transform_expr e rhs in
        mret (MkStatement tags (StatAssignment lhs' rhs') typ, e)
      | StatDirectApplication typ' args =>
        mret (MkStatement tags (StatDirectApplication typ' (transform_exprs e args)) typ, e)
      | StatConditional cond tru fls =>
        let cond' := transform_expr e cond in
        let* (tru', _) := transform_stmt e ns tru in
        let* fls' :=
          match fls with
          | Some fls => let* (fls', _) := transform_stmt e ns fls in mret (Some fls')
          | None => mret None
          end in
        mret (MkStatement tags (StatConditional cond' tru' fls') typ, e)
      | StatBlock block =>
        let* block' := transform_blk e ns block in
        mret (MkStatement tags (StatBlock block') typ, e)
      | StatExit => mret (MkStatement tags stmt typ, e)
      | StatEmpty => mret (MkStatement tags stmt typ, e)
      | StatReturn None => mret (MkStatement tags stmt typ, e)
      | StatReturn (Some expr) =>
        mret (MkStatement tags (StatReturn (Some (transform_expr e expr))) typ, e)
      | StatSwitch expr cases =>
        let expr' := transform_expr e expr in
        let* cases' := sequence (map (transform_ssc e ns) cases) in
        mret (MkStatement tags (StatSwitch expr' cases') typ, e)
      | StatConstant typ' name value _ =>
        let* name' := fresh name in
        let l := LocCons (ns ++ [name']) in
        let e' := IdentMap.set name l e in
        mret (MkStatement tags (StatConstant typ' name value l) typ, e')
      | StatVariable typ' name init _ =>
        let* name' :=  fresh name in
        let init' := option_map (transform_expr e) init in
        let l := LocCons (ns ++ [name']) in
        let e' := IdentMap.set name l e in
        mret (MkStatement tags (StatVariable typ' name init' l) typ, e')
      | StatInstantiation typ' args name init =>
        let args' := transform_exprs e args in
        let* init' :=
          match init with
          | Some init => let* init' := transform_blk e ns init in mret (Some init')
          | None => mret None
          end in
        mret (MkStatement tags (StatInstantiation typ' args' name init') typ, e)
      end
    with transform_stmt (e: env) (ns: list P4String) (stmt: @Statement tags_t):
           monad (@Statement tags_t * env) :=
           match stmt with
           | MkStatement tags stmt typ => transform_stmtpt e ns tags stmt typ
           end
    with transform_blk (e: env) (ns: list P4String) (blk: @Block tags_t): monad (@Block tags_t) :=
           match blk with
           | BlockEmpty tag => mret (BlockEmpty tag)
           | BlockCons stmt blk0 =>
             let* (stmt', e') := transform_stmt e ns stmt in
             let* blk0' := transform_blk e' ns blk0 in
             mret (BlockCons stmt' blk0')
           end
    with transform_ssc (e: env) (ns: list P4String) (ssc: @StatementSwitchCase tags_t):
           monad (@StatementSwitchCase tags_t) :=
           match ssc with
           | StatSwCaseAction tags label code =>
             let* code' := transform_blk e ns code in
             mret (StatSwCaseAction tags label code')
           | StatSwCaseFallThrough _ _ => mret ssc
           end.

  End transform_stmt.

  Definition with_state {T} (st: state) (m: monad T) : monad T :=
    fun st' => let (res, _) := m st in (res, st').

  Definition with_empty_state {T} (m: monad T): monad T :=
    with_state nil m.

  (* Definition 
  Definition add_name (global: bool) (name : P4String) (e: env): env :=
    IdentMap.set name (if global then LGlobal [name] else LInstance [name]) e.

  Definition add_name' (global: bool) (e: env) (name : P4String): env :=
    add_name global name e.

  Definition add_names (global: bool) (names: list P4String) (e: env): env :=
    fold_left (add_name' global) names e. *)

  Definition transform_decl_base (LocCons: list P4String -> @Locator tags_t) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    match decl with
    | DeclConstant tags typ name value _ =>
      let* name' := fresh name in
      let l := LocCons [name'] in
      let e' := IdentMap.set name l e in
      mret (DeclConstant tags typ name value l, e')
    | DeclInstantiation tags typ args name init =>
      let l := LocCons [name] in
      let e' := IdentMap.set name l e in
      mret (decl, e')
    (* let (local', n1) :=
      ((fix transform_decl_list (idx: N) (l: list (@Declaration tags_t)):
          (list (@Declaration tags_t) * N) :=
          match l with
          | nil => (nil, idx)
          | x :: rest =>
            let (l2, n2) := transform_decl idx x in
            let (l3, n3) := transform_decl_list n2 rest in (l2 ++ l3, n3)
          end) nameIdx locals) in
    let (blk, n2) := transform_blk n1 appl in
    ([DeclControl tags name type_params params cparams local' blk], n2) *)
    | DeclFunction tags ret name type_params params body =>
      (* Functions can only be defined at the top level. *)
      let* body' := with_empty_state (transform_blk LocCons e [name] body) in
      let l := LocCons [name] in
      let e' := IdentMap.set name l e in
      mret (DeclFunction tags ret name type_params params body', e')
    | DeclExternFunction _ _ _ _ _ => mret (decl, e) (* TODO *)
    | DeclVariable tags typ name init _ =>
      let* name' :=  fresh name in
      let init' := option_map (transform_expr e) init in
      let l := LocCons [name'] in
      let e' := IdentMap.set name l e in
      mret (DeclVariable tags typ name init' l, e')
    | DeclValueSet tags typ size name =>
      mret (decl, e) (* TODO *)
    (* let (l1e1, n1) := transform_Expr nameIdx size in
    let (l1, e1) := l1e1 in
    (map expr_to_decl l1 ++ [DeclValueSet tags typ e1 name], n1) *)
    | DeclAction tags name data_params ctrl_params body =>
      let* body' := with_empty_state (transform_blk LocCons e [name] body) in
      let l := LocCons [name] in
      let e' := IdentMap.set name l e in
      mret (DeclAction tags name data_params ctrl_params body', e')
    | DeclTable tags name key actions entries default_action size
            custom_properties =>
      mret (decl, e) (* TODO *)
    (* let (l1e1, n1) := transform_list transform_tblkey nameIdx key in
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
    (l1 ++ l2 ++ l3 ++ l5 ++ l6 ++ [DeclTable tags name e1 e2 e3 e5 size e6], n6) *)
    | _ => mret (decl, e)
    end.

  Fixpoint transform_decls_base (LocCons: list P4String -> @Locator tags_t)
      (e: env) (decls: list (@Declaration tags_t)):
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls0 =>
      let* (decl', e') := transform_decl_base LocCons e decl in
      let* (decls0', e'') := transform_decls_base LocCons e' decls0 in
      mret (decl' :: decls0', e'')
    end.

  Definition transform_decl (LocCons: list P4String -> @Locator tags_t) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    match decl with
    | DeclParser tags name type_params params cparams locals states =>
      mret (decl, e) (* TODO *)
    (* let (local', n1) :=
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
    (local' ++ l2 ++ [DeclParser tags name type_params params cparams local' s2], n1) *)
    | DeclControl tags name type_params params cparams locals apply =>
      (* let transform_control (e: env) (locals: list (@Declaration tags_t))
          (apply: @Block tags_t): monad (list (@Declaration tags_t) * @Block tags_t) :=
        let* (locals', e') := transform_decls' transform_decl LInstance e locals in
        let* apply' := transform_blk LInstance e' nil apply in
        mret (locals', apply') in *)
      (* TODO We need to put params in env and used_list. *)
      let used_list := summarize_control locals apply in
      let inner_scope_monad := (
        let* (locals', e') := transform_decls_base LInstance e locals in
        let* apply' := transform_blk LInstance e' nil apply in
        mret (locals', apply')
      ) in
      let* (locals', apply') := with_state used_list inner_scope_monad in
      let l := LocCons [name] in
      let e' := IdentMap.set name l e in
      mret (DeclControl tags name type_params params cparams locals' apply', e')
    | _ => transform_decl_base LocCons e decl
    end.

  Fixpoint transform_decls (LocCons: list P4String -> @Locator tags_t) (e: env) (decls: list (@Declaration tags_t)):
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls' =>
      let* (decl', e') := transform_decl LocCons e decl in
      let* (decls'', e'') := transform_decls LocCons e decls' in
      mret (decl' :: decls'', e'')
    end.

  Definition transform_prog (prog: @program tags_t): @program tags_t + exception :=
    match prog with
    | Program decls =>
      match (transform_decls LGlobal IdentMap.empty decls) nil with
      | (inl (decls', _), _) => inl (Program decls')
      | (inr ex, _) => inr ex
      end
    end.

End Transformer.
