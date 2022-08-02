Set Warnings "-custom-entry-overridden".
From Coq Require Import Program.Basics Arith.EqNat String List.
From Poulet4 Require Export P4cub.Syntax.AST P4cub.Syntax.CubNotations.
From Poulet4 Require Export
     Utils.P4Arith Utils.Envn
     P4cub.Semantics.Dynamic.BigStep.BigStep
     Monads.Result Compile.ToP4cub
     Utils.Util.StringUtil Utils.Util.ListUtil.
Import Env.EnvNotations Result ResultNotations.

Open Scope string_scope.

(** Compile to GCL *)
Module ST := Stmt.
Module CD := Control.
Module TD := TopDecl.
Module E := Expr.
Module F := F.

Section Inline.
Variable tags_t : Type.



(* this needs to be changed to an array access *)
(*Left and right brackets for array accesses *)
Definition AAL := "$_". (* evoke [ *)
Definition AAR := "_$". (* evoke ] *)
Definition index_array_str s idx :=
  s ++ AAL ++ string_of_nat idx ++ AAR.

Definition expenv : Type := Env.t string (E.e tags_t).

Definition get_exp (pa : paramarg (E.e tags_t) (E.e tags_t)) :=
  match pa with
  | PAInOut e => e
  | PAIn e => e
  | PAOut e => e
  | PADirLess e => e
  end.

Definition args_to_expenv (args : F.fs string (paramarg (E.e tags_t) (E.e tags_t))) : expenv :=
  F.fold (fun param arg env => Env.bind param (get_exp arg) env) args [].

Fixpoint subst_e (η : expenv) (e : E.e tags_t) : E.e tags_t :=
  match e with
  | E.EBool _ _ => e
  | E.EBit _ _ _ => e
  | E.EInt _ _ _ => e
  | E.EVar type x i =>
    match Env.find x η with
    | None => e
    | Some e' => e'
    end
  | E.ESlice e hi lo i =>
    E.ESlice (subst_e η e) hi lo i
  | E.ECast type arg i =>
    E.ECast type (subst_e η arg) i
  | E.EUop op type arg i =>
    E.EUop op type (subst_e η arg) i
  | E.EBop t op l r i =>
    E.EBop t op (subst_e η l) (subst_e η r) i
  | E.ETuple es i =>
    E.ETuple (List.map (subst_e η) es) i
  | E.EStruct fields i =>
    E.EStruct (F.map (subst_e η) fields) i
  | E.EHeader fields valid i =>
    E.EHeader (F.map (subst_e η) fields) (subst_e η valid) i
  | E.EExprMember mem expr_type arg i =>
    E.EExprMember mem expr_type (subst_e η arg) i
  | E.EError _ _ => e
  | E.EHeaderStack fields headers ni i =>
    E.EHeaderStack fields (List.map (subst_e η) headers) ni i
  | E.EHeaderStackAccess fs stack idx i =>
    E.EHeaderStackAccess fs (subst_e η stack) idx i
  end.

Inductive t : Type :=
| ISkip (i : tags_t)                       (* skip, useful for
                                               small-step semantics *)
| IVardecl (type : E.t)
           (x : string) (i : tags_t)       (* Variable declaration. *)
| IAssign (type : E.t) (lhs rhs : E.e tags_t)
          (i : tags_t)                     (* assignment *)
| IConditional (guard_type : E.t)
               (guard : E.e tags_t)
               (tru_blk fls_blk : t) (i : tags_t) (* conditionals *)
| ISeq (s1 s2 : t) (i : tags_t)                   (* sequences *)
| IBlock (blk : t)                                (* blocks *)
| IReturnVoid (i : tags_t)                        (* void return statement *)
| IReturnFruit (t : E.t)
               (e : E.e tags_t)(i : tags_t)       (* fruitful return statement *)
| IExit (i : tags_t)                              (* exit statement *)
| IInvoke (x : string)
          (keys : list (E.t * E.e tags_t * E.matchkind))
          (actions : list (string * t))
          (i : tags_t)
| ISetValidity (hdr: E.e tags_t ) (val : bool) (i : tags_t) (*set the header indicated by hdr to valid (if val is true) or invalid (if val is false) *)
| IHeaderStackOp (hdr_stck_name : string) (typ : E.t) (op : ST.hsop) (size : positive) (i : tags_t)
| IExternMethodCall (extn : string) (method : string) (args : E.arrowE tags_t) (i : tags_t).

Definition assume b tags :=
  let args := {| paramargs:=[ ("check", PAIn b) ] ; rtrns:=None |} in
  IExternMethodCall "_" "assume" args tags.

Definition rename_string (table action x : string) (params : list string) :=
  if fold_right (fun y => orb (String.eqb x y)) false params
  then "_symb$" ++ table ++ "$" ++ action ++ "$arg$" ++ x
  else x.

Fixpoint action_param_renamer_expr (table action : string) (params : list string) (e : E.e tags_t) : E.e tags_t :=
  match e with
  | E.EBool _ _ => e
  | E.EBit _ _ _ => e
  | E.EInt _ _ _ => e
  | E.EVar type x i =>
    E.EVar type (rename_string table action x params) i
  | E.ESlice e hi lo i =>
    E.ESlice (action_param_renamer_expr table action params e) hi lo i
  | E.ECast typ arg i =>
    E.ECast typ (action_param_renamer_expr table action params arg) i
  | E.EUop op typ arg i =>
    E.EUop op typ (action_param_renamer_expr table action params arg) i
  | E.EBop t op le re i =>
    let le' := action_param_renamer_expr table action params le in
    let re' := action_param_renamer_expr table action params re in
    E.EBop t op le re i
  | E.ETuple es i =>
    E.ETuple (List.map (action_param_renamer_expr table action params) es) i
  | E.EStruct fields i =>
    E.EStruct (F.map (action_param_renamer_expr table action params) fields) i
  | E.EHeader fields valid i =>
    E.EHeader (F.map (action_param_renamer_expr table action params) fields) (action_param_renamer_expr table action params valid) i
  | E.EExprMember mem expr_type arg i =>
    E.EExprMember mem expr_type (action_param_renamer_expr table action params arg) i
  | E.EError _ _ => e
  | E.EHeaderStack fields headers ni i =>
    E.EHeaderStack fields (List.map (action_param_renamer_expr table action params) headers) ni i
  | E.EHeaderStackAccess fs stack idx i =>
    E.EHeaderStackAccess fs (action_param_renamer_expr table action params stack) idx i
  end.

Fixpoint action_param_renamer (table action : string) (params : list string) (c : t) : result (t * list string) :=
  match c with
  | ISkip _ => ok (c, params)
  | IVardecl type x i => ok (c, filter (negb ∘ (String.eqb x)) params)
  | IAssign t lhs rhs i =>
    let rhs' := action_param_renamer_expr table action params rhs in
    let lhs' := action_param_renamer_expr table action params lhs in
    ok (IAssign t lhs' rhs' i, params)
  | IConditional typ cond tru fls i =>
    let cond' := action_param_renamer_expr table action params cond in
    let* (tru', _) := action_param_renamer table action params tru in
    let+ (fls', _) := action_param_renamer table action params fls in
    (IConditional typ cond' tru' fls' i, params)
  | ISeq c1 c2 i =>
    let* (c1', params1) := action_param_renamer table action params c1 in
    let+ (c2', params2) := action_param_renamer table action params1 c2 in
    (ISeq c1' c2' i, params2)
  | IBlock blck =>
    let+ (blck', _) := action_param_renamer table action params blck in
    (blck', params)
  | IReturnVoid _ => ok (c, params)
  | IReturnFruit t e i =>
    let e' := action_param_renamer_expr table action params e in
    ok (IReturnFruit t e' i, params)
  | IExit _ => ok (c, params)
  | IInvoke _ _ _ _ =>
    error "Invocations should not occur within actions"
  | ISetValidity e v i =>
    let e' := action_param_renamer_expr table action params e in
    ok (ISetValidity e' v i, params)
  | IHeaderStackOp hdr_stck_name typ hsop size i =>
    ok (IHeaderStackOp (rename_string hdr_stck_name table action params) typ hsop size i, params)
  | IExternMethodCall extn method ar i =>
    let pargs := paramargs ar in
    let ret := rtrns ar in
    let pargs' := F.fold (fun p a rst =>
          let a' := paramarg_map (action_param_renamer_expr table action params)
                                 (action_param_renamer_expr table action params) a in
          (p, a') :: rst) [] pargs in
    let ar' := {| paramargs := pargs'; rtrns := ret |} in
    ok (IExternMethodCall extn method ar' i, params)
  end.

Fixpoint subst_t (η : expenv) (c : t) : (t * expenv) :=
  match c with
  | ISkip i => (ISkip i, η)
  | IVardecl type x i  =>
    (IVardecl type x i, Env.remove x η)
  | IAssign t lhs rhs i =>
    (IAssign t (subst_e η lhs) (subst_e η rhs) i , η)
  | IConditional guard_type guard tru_blk fls_blk i =>
    (IConditional guard_type
                  (subst_e η guard)
                  (fst (subst_t η tru_blk))
                  (fst (subst_t η fls_blk))
                  i, η)
  | ISeq s1 s2 i =>
    let (s1', η1) := subst_t η s1 in
    let (s2', η2) := subst_t η1 s2 in
    (ISeq s1' s2' i, η2)
  | IBlock blk =>
    (IBlock (fst (subst_t η blk)), η)
  | IReturnVoid _ => (c, η)
  | IReturnFruit t e i => (IReturnFruit t (subst_e η e) i,η)
  | IExit _ => (c,η)
  | IInvoke x keys actions i =>
    let keys' := List.map (fun '(t, m,k) => (t, subst_e η m, k)) keys in
    let actions' := List.map (fun '(s,a) => (s, fst(subst_t η a))) actions in
    (IInvoke x keys' actions' i, η)

  | IExternMethodCall extn method ar i =>
    let pas := paramargs ar in
    let returns := rtrns ar in
    let pas' := F.map (paramarg_map (subst_e η) (subst_e η)) pas in
    let ar' := {| paramargs := pas'; rtrns:=returns |} in
    (IExternMethodCall extn method ar' i, η)
  | ISetValidity e v i =>
    (ISetValidity (subst_e η e) v i, η)
  | IHeaderStackOp hdr_stck_name stck_el_typ hsop size i =>
    match Env.find hdr_stck_name η with
    | None => (c, η)
    | Some e' =>
      let stck_type := t_of_e e' in
      (ISeq (IAssign stck_type (E.EVar stck_type hdr_stck_name i) e' i) c i, η)
    end
  end.

Definition copy (args : E.args tags_t) : expenv :=
  F.fold (fun param arg η => match arg with
                             | PAIn e => Env.bind param e η
                             | PAInOut e => Env.bind param e η
                             | PAOut e => Env.bind param e η
                             | PADirLess e => Env.bind param e η
                             end)
         args (Env.empty String.string (E.e tags_t)).

Definition string_list_of_params (ps : E.params) : list string :=
  List.map fst ps.

Fixpoint elaborate_arg_expression (param : string) (arg : E.e tags_t) : F.fs string (E.e tags_t) :=
  let access := fun s f => s ++ "." ++ f in
  let is_valid := fun tags => let one_bit := E.TBit (BinNat.N.of_nat 1) in
                              (access param "is_valid",
                               E.EExprMember one_bit "is_valid" arg tags) in
  let member_member := fun f t tags => E.EExprMember t f arg tags in
  let loop := fun tags '(f, t) acc => (access param f, member_member f t tags) :: acc in
  match arg with
  | E.EVar (E.TStruct fs) x tags =>
    List.fold_right (fun '(f, t) acc =>
     (access param f, (E.EExprMember t f arg tags)) :: acc) [] fs
  | E.EVar (E.THeader fs) x tags =>
    List.fold_right (loop tags) [is_valid tags] fs
  | E.EExprMember (E.TStruct fs) mem _ tags =>
    List.fold_right (loop tags) [] fs
  | E.EExprMember (E.THeader fs) mem _ tags  =>
    List.fold_right (loop tags) [is_valid tags] fs
  | E.EVar (E.TTuple ts) x tags =>
    ListUtil.fold_righti (fun idx t acc => (index_array_str param idx, (E.EVar t (index_array_str x idx) tags)) :: acc) [] ts
  | E.ETuple es _ =>
    ListUtil.fold_righti (fun i e acc =>
          let param_i := index_array_str param i in
          let es := elaborate_arg_expression param_i e in
          List.app es acc) [] es
  | E.EHeaderStackAccess fs stk idx tags =>
    List.fold_right (loop tags) [is_valid tags] fs
  | _ => [(param, arg)]
  end.

Definition paramarg_map_union {A B : Type} (f : A -> F.fs string B) (pa : paramarg A A) : F.fs string (paramarg B B) :=
  match pa with
  | PAIn a => F.map PAIn (f a)
  | PAOut a => F.map PAOut (f a)
  | PAInOut a => F.map PAInOut (f a)
  | PADirLess a => F.map PADirLess (f a)
  end.

Definition elaborate_argument (parg : F.f string (paramarg (E.e tags_t) (E.e tags_t))) : F.fs string (paramarg (E.e tags_t) (E.e tags_t)) :=
  let '(param, arg) := parg in
  paramarg_map_union (elaborate_arg_expression param) arg.


Definition elaborate_arguments (args : F.fs string (paramarg (E.e tags_t) (E.e tags_t))) :  F.fs string (paramarg (E.e tags_t) (E.e tags_t)) :=
  List.concat (List.map elaborate_argument args).

Definition elaborate_arrowE (ar : E.arrowE tags_t) : E.arrowE tags_t :=
  {| paramargs := elaborate_arguments ar.(paramargs);
     rtrns := ar.(rtrns) |}.

Definition realize_symbolic_key (symb_var : string) (key_type : E.t) (key : E.e tags_t) (mk : E.matchkind) (tags : tags_t) :=
  let symb_key := E.EVar key_type symb_var tags in
  let assume := assume (E.EBop E.TBool E.Eq symb_key key tags) tags in
  match mk with
  | E.MKExact =>
    (symb_key, assume, E.EBool false tags)
  | _ =>
    (symb_key, assume, E.EVar E.TBool (symb_var ++ "$DONTCARE") tags)
  end.

Fixpoint normalize_keys_aux t (keys : list (E.t * E.e tags_t * E.matchkind)) i tags :=
  let keyname := "_symb$" ++ t ++ "$match_" ++ string_of_nat i in
  match keys with
  | [] => (ISkip tags, [])
  | ((key_type, key_expr, key_mk)::keys) =>
    let (assumes, new_keys) := normalize_keys_aux t keys (i+1) tags in
    let '(symb_key, assgn, skip_eq) := realize_symbolic_key keyname key_type key_expr key_mk tags in
    let new_assume := IConditional E.TBool skip_eq (ISkip tags) assgn tags in
    (ISeq new_assume assumes tags, (key_type, symb_key, key_mk)::new_keys)
  end.

Definition normalize_keys t keys := normalize_keys_aux t keys 0.

Definition get_state_name state :=
  match state with
  | Parser.STStart => "start"
  | Parser.STAccept => "accept"
  | Parser.STReject => "reject"
  | Parser.STName s => s
  end.

Definition state_flag_name name := "_state$" ++ name ++ "$next".
Definition state_flag name tags : E.e tags_t := E.EVar E.TBool (state_flag_name name) tags.
Definition set_state_flag name value tags := IAssign E.TBool (state_flag name tags) (E.EBool value tags) tags.
Definition construct_state name stmt trans tags :=
  IConditional E.TBool
               (state_flag name tags)
               (ISeq (set_state_flag name false tags)
                     (ISeq stmt trans tags) tags)
               (ISkip tags) tags.

Definition extract_single (es : list (E.e tags_t)) (msg : string) : result (E.e tags_t) :=
  match es with
  | [e] => ok e
  | _ => error msg
  end.

Fixpoint elim_tuple_expr (e : E.e tags_t) :=
  match e with
  | E.EBool _ _
  | E.EBit _ _ _
  | E.EInt _ _ _ => ok [e]
  | E.EVar _ _ _ =>
    (* TODO a var can (?) be a tuple, need to inline it here. *)
    ok [e]
  | E.ESlice _ _ _ _ =>
    (* A tuple cannot be sliced *)
    ok [e]
  | E.ECast t e tags =>
    let* es := elim_tuple_expr e in
    let+ e := extract_single es "TypeError: tuples cannot be cast" in
    [E.ECast t e tags]
  | E.EUop t op e tags =>
    (* THere are no unary operations that operate on Tuples *)
    let* es := elim_tuple_expr e in
    let+ e := extract_single es "TypeError: no unary operators for tuples" in
    [E.EUop t op e tags]
  | E.EBop t op e e' tags =>
    match op with
    | E.Eq =>
      let* es  := elim_tuple_expr e in
      let* es' := elim_tuple_expr e' in
      let+ eq_pairs := zip es es' in
      let eq := fun e1 e2 => E.EBop E.TBool E.Eq e1 e2 tags in
      let and := fun e1 e2 => E.EBop E.TBool E.And e1 e2 tags in
      [fold_right (fun '(e1,e2) => and (eq e1 e2))
                  (E.EBool true tags)
                  eq_pairs]
    | _ =>
      let* es  := elim_tuple_expr e in
      let* es' := elim_tuple_expr e' in
      let* e := extract_single es "TypeError: (=) is the only binary op on tuples got something else" in
      let+ e' := extract_single es' "TypeError: (=) is the only binary op on tuples got something else" in
      [E.EBop t op e e' tags]
    end
  | E.ETuple es tags =>
    let+ ees := rred (List.map elim_tuple_expr es) in
    List.concat ees
  | _ =>
  (* TODO Figure out what to do more complicated types *)
    ok [e]
  end.


Definition translate_simple_patterns pat tags : result (E.e tags_t) :=
  match pat with
  | Parser.PATBit w v =>
    ok (E.EBit w v tags)
  | Parser.PATInt w v =>
    ok (E.EInt w v tags)
  | _ =>
    error "pattern too complicated, expecting int or bv literal"
  end.




Program Fixpoint translate_pat tags e pat { struct pat } : result (E.e tags_t)  :=
  let bool_op := fun o x y => E.EBop E.TBool o x y tags in
  let mask := fun t x y => E.EBop t E.BitAnd x y tags in
  let and := bool_op E.And in
  let eq := bool_op E.Eq in
  let le := bool_op E.Le in
  match pat with
  | Parser.PATWild =>
    ok (E.EBool true tags)
  | Parser.PATMask pat msk =>
    let* e_pat := translate_simple_patterns pat tags in
    let+ e_msk := translate_simple_patterns msk tags in
    let t := t_of_e e_pat in
    eq (mask t e e_msk) (mask t e_pat e_msk)
  | Parser.PATRange lo hi =>
    let* e_lo := translate_simple_patterns lo tags in
    let+ e_hi := translate_simple_patterns hi tags in
    and (le e e_hi)
        (le e_lo e)
  | Parser.PATBit _ _
  | Parser.PATInt _ _ =>
    let+ e_pat := translate_simple_patterns pat tags in
    eq e e_pat
  | Parser.PATTuple pats =>
    let* es := elim_tuple_expr e in
    let+ matches :=
       ListUtil.fold_lefti
       (fun i p acc => let* acc := acc in
                       let* e := ListUtil.ith es i in
                       let+ cond := translate_pat tags e p in
                       and acc cond)
       (ok (E.EBool true tags)) pats
    in
    matches
  end.

Definition lookup_parser_state name states : option (Parser.state_block tags_t) :=
  F.find_value (String.eqb name) states.

Definition lookup_parser_states (names : list string) states :=
  List.fold_right (fun n acc =>
   if String.eqb n "accept" || String.eqb n "reject"
   then acc
   else match lookup_parser_state n states with
        | None => acc
        | Some s => (n,s) :: acc
        end) [] names.

Definition init_parser (states : F.fs string (Parser.state_block tags_t)) (tags : tags_t) :=
  F.fold (fun f _ acc => if String.eqb f "start"
                         then ISeq (set_state_flag f true tags) acc tags
                         else ISeq (set_state_flag f false tags) acc tags)
         states
         (ISeq (set_state_flag "accept" false tags) (set_state_flag "reject" false tags) tags).

Open Scope list_scope.
(* Fixpoint inline_state *)
(*          (gas : nat) *)
(*          (unroll : nat) *)
(*          (ctx : DeclCtx tags_t) *)
(*          (name : string) *)
(*          (state : Parser.state_block tags_t) *)
(*          (states : F.fs string (Parser.state_block tags_t)) *)
(*          (tags : tags_t) *)
(*   : result ((list (string * Parser.state_block tags_t)) * t) := *)
(*   match gas with *)
(*   | O => ok ([], ISkip tags) *)
(*   | S gas => *)
(*     let* stmt := inline gas unroll ctx (Parser.stmt state) in *)
(*     let+ (neighbor_names, trans) := inline_transition gas unroll ctx name (Parser.trans state) tags in *)
(*     let neighbor_states := lookup_parser_states neighbor_names states in *)
(*     (neighbor_states, construct_state name stmt trans tags) *)
(*   end *)
(* with inline_transition (gas : nat) *)
(*                        (unroll : nat) *)
(*                        (ctx : DeclCtx tags_t) *)
(*                        (name : string) *)
(*                        (trans : Parser.e tags_t ) *)
(*                        (tags : tags_t) *)
(*      : result ((list string) * t)  := *)
(*        match gas with *)
(*        | O => ok ([], ISkip tags) *)
(*        | S gas => *)
(*          match trans with *)
(*          | Parser.PGoto state tags => *)
(*            let name := get_state_name state in *)
(*            ok ([name], set_state_flag name true tags) *)
(*          | Parser.PSelect discriminee default states tags => *)
(*            let default := inline_transition gas unroll ctx name default tags in *)
(*            let inline_trans_loop := fun '(pat, trans) acc  => *)
(*                     let* (states, inln) := acc in *)
(*                     let* cond := translate_pat tags discriminee pat in *)
(*                     let+ (new_states, trans) := inline_transition gas unroll ctx name trans tags in *)
(*                     (states ++ new_states, IConditional E.TBool cond trans inln tags) in *)
(*            List.fold_right inline_trans_loop default states *)
(*          end *)
(*        end *)
Print Parser.PSelect.
Print Parser.e.
Print Parser.state.
Print List.find.
Print List.fold_left.
Fixpoint inline_parser (gas : nat)
                   (unroll : nat)
                   (tags : tags_t)
                   (ctx : DeclCtx tags_t)
                   (seen : list string)
                   (current_name : string)
                   (current : Parser.state_block tags_t)
                   (states : F.fs string (Parser.state_block tags_t))
     : result t :=
       match gas with
       | O => ok (ISkip tags)
       | S gas =>
         let* stmt := inline gas unroll ctx (Parser.stmt current) in
         let+ trans := inline_transition gas unroll tags ctx seen current_name (Parser.trans current) states in
         ISeq stmt trans tags
       end
with inline_transition gas unroll tags ctx seen current_name trans states : result t :=
       match gas with
       | O => ok (ISkip tags)
       | S gas =>
         match trans with
         | Parser.PGoto Parser.STStart tags =>
           error "should not transition back to start state"
         | Parser.PGoto Parser.STAccept tags =>
           ok (set_state_flag "accept" true tags)
         | Parser.PGoto Parser.STReject tags =>
           ok (set_state_flag "reject" true tags)
         | Parser.PGoto (Parser.STName st) tags =>
           match lookup_parser_state st states with
           | None => error (String.append "unknown parser state" st)
           | Some pstate =>
             let unroll := if List.find (String.eqb st) seen then unroll-1 else unroll in
             if Nat.eqb unroll 0
             then ok (set_state_flag "reject" true tags)
             else inline_parser gas unroll tags ctx (st::seen) st pstate states
           end
         | Parser.PSelect discriminee default cases tags =>
           let inline_default := inline_transition gas unroll tags ctx seen current_name default states in
           let f acc_r '(pat, trans) :=
               let* acc := acc_r in
               let* cond := translate_pat tags discriminee pat in
               let+ inln := inline_transition gas unroll tags ctx seen current_name trans states in
               IConditional E.TBool cond inln acc tags
               in
           List.fold_left f (List.rev' cases) inline_default
         end
       end
with inline (gas : nat)
            (unroll : nat)
            (ctx : DeclCtx tags_t)
            (s : ST.s tags_t)
  : result t :=
  match gas with
  | O => error "Inliner ran out of gas"
  | S gas =>
    match s with
    | ST.SSkip i =>
      ok (ISkip i)
    | ST.SVardecl x t_or_e i =>
      match t_or_e with
      | inl t =>  ok (IVardecl t x i)
      | inr e =>
        let t := t_of_e e in
        ok (ISeq (IVardecl t x i) (IAssign t (E.EVar t x i) e i) i)
      end
    | ST.SAssign lhs rhs i =>
      ok (IAssign (t_of_e rhs) lhs rhs i)

    | ST.SConditional guard tru_blk fls_blk i =>
      let* tru_blk' := inline gas unroll ctx tru_blk in
      let+ fls_blk' := inline gas unroll ctx fls_blk in
      IConditional (t_of_e guard) guard tru_blk' fls_blk' i

    | ST.SSeq s1 s2 i =>
      let* i1 := inline gas unroll ctx s1 in
      let+ i2 := inline gas unroll ctx s2 in
      ISeq i1 i2 i

    | ST.SBlock s =>
      let+ blk := inline gas unroll ctx s in
      IBlock blk

    | ST.SFunCall f _ ar i =>
      let args := paramargs ar in
      let ret := rtrns ar in
      match find_function _ ctx f with
      | Some (TD.TPFunction _ _ _ body i) =>
        (** TODO check copy-in/copy-out *)
        let+ rslt := inline gas unroll ctx body in
        let (s,_) := subst_t (args_to_expenv args) rslt in
        IBlock s
      | Some _ =>
        error "[ERROR] Got a nonfunction when `find`ing a function"
      | None =>
        let args := elaborate_arrowE {|paramargs:=args; rtrns:=ret|} in
        ok (IExternMethodCall "_" f args i)
      end

    | ST.SActCall a args i =>
      let* adecl := from_opt (find_action tags_t ctx a) ("could not find action " ++ a ++ " in environment") in
      match adecl with
      | CD.CDAction _ _ body i =>
        (** TODO handle copy-in/copy-out *)
        let+ rslt := inline gas unroll ctx body in
        let η := args_to_expenv args in
        IBlock (fst (subst_t η rslt))
      | _ =>
        error "[ERROR] got a nonaction when `find`-ing a function"
      end

    | ST.SApply inst ext_args args tags =>
      match find_control _ ctx inst with
      | None =>
        let parser := find_parser _ ctx inst in
        let* pinst := from_opt parser ("could not find controller or parser named " ++ inst) in
        match pinst with
        | TD.TPInstantiate pname _ _ pargs tags =>
          let pdecl_opt := find_parser _ ctx pname in
          let* pdecl := from_opt pdecl_opt ("could not find parser of type " ++ pname) in
          match pdecl with
          | TD.TPParser _ _ _ _ start states tags =>
            let+ parser := inline_parser gas unroll tags ctx ["start"] "start" start states in
            let init := init_parser states tags in
            ISeq init  parser tags
          (* error ("found parser " ++ inst ++ " of type " ++ pname ++ " [TODO] translate the parser!") *)
          | _ =>
            error ("expected `" ++ pname ++ "` to be a parser declaration, but it was something else")
          end
        | _ =>
          error ("expected `" ++ inst ++ "` to be a instantiation, but it was something else")
        end
      | Some cinst =>
        match cinst with
        | TD.TPInstantiate cname _ _ cargs i =>
          let cdecl_opt := find_control tags_t ctx cname in
          let* cdecl := from_opt cdecl_opt "could not find controller" in
          match cdecl with
          | TD.TPControl _ _ _ _ body apply_blk i =>
            (* Context is begin extended with body, but why can't I find the controls? *)
            let ctx' := of_cdecl tags_t ctx body in
            let+ rslt := inline gas unroll ctx' apply_blk in
            (** TODO check copy-in/copy-out *)
            let η := copy args in
            IBlock (fst (subst_t η rslt))
          | _ =>
            error "Expected a control decl, got something else"
          end
        | _ =>
          error "Expected a control instantiation, got something else"
        end
      end
    | ST.SReturn None i =>
      ok (IReturnVoid i)

    | ST.SReturn (Some expr) i =>
      ok (IReturnFruit (t_of_e expr) expr i)

    | ST.SExit i =>
      ok (IExit i)

    | ST.SInvoke tbl_name i =>
      let* tdecl := from_opt (find_table tags_t ctx tbl_name) "could not find table in environment" in
      match tdecl with
      | CD.CDTable _ tbl _ =>
        let keys := List.map (fun '(e,k) => (t_of_e e, e, k)) (Control.table_key tbl) in
        let actions := Control.table_actions tbl in
        let act_size := Nat.max (PeanoNat.Nat.log2_up (List.length actions)) 1 in
        let act_sizeN := BinNat.N.of_nat act_size in
        let act_type := E.TBit act_sizeN in
        let act_to_gcl := fun i a acc_res =>
          let* acc := acc_res in
          let* act := from_opt (find_action tags_t ctx a) ("could not find action " ++ a ++ " in environment") in
          match act with
          | CD.CDAction _ params body tags =>
            let* s := inline gas unroll ctx body in
            let+ (s', _) := action_param_renamer tbl_name a (string_list_of_params params) s in
            let set_action_run :=
                IAssign act_type
                          (E.EVar act_type ("_return$" ++ tbl_name ++ ".action_run") tags)
                          (E.EBit act_sizeN (BinInt.Z.of_nat i) tags) tags
            in
            (ISeq set_action_run s' tags) :: acc
          | _ =>
            error "[ERROR] expecting action when `find`ing action, got something else"
          end
        in
        let* acts := fold_lefti act_to_gcl (ok []) actions in
        let+ named_acts := zip actions acts in
        let (assumes, keys') := normalize_keys tbl_name keys i in
        let invocation := IInvoke tbl_name keys' named_acts i in
        ISeq assumes invocation i
      | _ =>
        error "[ERROR] expecting table when getting table, got something else"
      end

    | ST.SExternMethodCall ext method _ args i =>
      ok (IExternMethodCall ext method args i)

    | ST.SSetValidity e b i =>
      ok (ISetValidity e b i)

    | ST.SHeaderStackOp s typ op n i =>
      ok (IHeaderStackOp s typ op n i)
    end
  end.

Open Scope string_scope.
Definition seq_tuple_elem_assign
           (tuple_name : string)
           (i : tags_t)
           (n : nat)
           (p : E.t * E.e tags_t)
           (acc : Inline.t) : Inline.t :=
  let (t, e) := p in
  let tuple_elem_name := tuple_name ++ "__tup__" ++ string_of_nat n in
  let lhs := E.EVar t tuple_elem_name i in
  Inline.ISeq (Inline.IAssign t lhs e i) acc i.

Fixpoint elim_tuple_assign (ltyp : E.t) (lhs rhs : E.e tags_t) (i : tags_t) : result Inline.t :=
  match lhs, rhs with
  | E.EVar (E.TTuple types) x i, E.ETuple es _ =>
    let+ te := zip types es in
    fold_lefti (seq_tuple_elem_assign x i) (Inline.ISkip i) te
  | _,_ => ok (Inline.IAssign ltyp lhs rhs i)
  end.

Definition res_snd { A B : Type } (p : A * result B ) : result (A * B) :=
  match p with
  | (_, Error _ s) => error s
  | (a, Ok _ b) => ok (a, b)
  end.

Definition elaborate_tuple_literal
           (param : string)
           (ctor : E.e tags_t -> paramarg (E.e tags_t) (E.e tags_t))
           (es : list (E.e tags_t))
           (args : F.fs string (paramarg (E.e tags_t) (E.e tags_t))) :=
  ListUtil.fold_righti (fun idx e acc =>
   let index := fun s =>  index_array_str s idx in
   (index param, ctor e) :: acc) args es.

Fixpoint elim_tuple (c : Inline.t) : result t :=
  match c with
  | ISkip _ => ok c
  | IVardecl _ _ _ => ok c
  | IAssign type lhs rhs i =>
    elim_tuple_assign type lhs rhs i
  | IConditional typ g tru fls i =>
    let* gs' := elim_tuple_expr g in
    let* g' := extract_single gs' "TypeError conditional must be a singleton" in
    let* tru' := elim_tuple tru in
    let+ fls' := elim_tuple fls in
    IConditional typ g' tru' fls' i
  | ISeq c1 c2 i =>
    let* c1' := elim_tuple c1 in
    let+ c2' := elim_tuple c2 in
    ISeq c1' c2' i
  | IBlock blk =>
    let+ blk' := elim_tuple blk in
    IBlock blk'
  | IReturnVoid _ => ok c
  | IReturnFruit _ _ _ => ok c
  | IExit _ => ok c
  | IInvoke x keys actions i =>
    (** TODO do we need to eliminate tuples in keys??*)
    let+ actions := List.fold_right (fun '(name, act) acc =>
                     let* act := elim_tuple act in
                     let+ acc := acc in
                     (name, act) :: acc) (ok []) actions in
    IInvoke x keys actions i
  | IExternMethodCall extern method arrow tags =>
    let arrow := elaborate_arrowE arrow in
    ok (IExternMethodCall extern method arrow tags)
  | ISetValidity _ _ _ =>
    (** TODO do we need to eliminate tuples in valid sets? I think that'd be ill-typed *)
    ok c
  | IHeaderStackOp _ _ _ _ _ =>
    ok c
  end.

Fixpoint header_fields (tags : tags_t) (e : E.e tags_t) (fields : F.fs string E.t) : list (E.e tags_t * E.t)  :=
  (* TODO Type of ExprMember might need to be the header type *)
  F.fold (fun f typ acc => (E.EExprMember typ f e tags, typ) :: acc )
         fields
         [(E.EUop E.TBool E.IsValid e tags, E.TBool)].

Fixpoint header_elaboration_assign tags (lhs rhs : E.e tags_t) (fields : F.fs string E.t) : result t:=
  let lhs_members := header_fields tags lhs fields in
  let rhs_members := header_fields tags rhs fields in
  let+ assigns := zip lhs_members rhs_members  in
  let f := fun '((lhs_mem, typ), (rhs_mem, _)) acc => ISeq (IAssign typ lhs_mem rhs_mem tags) acc tags in
  List.fold_right f (ISkip tags) assigns.

Fixpoint elaborate_headers (c : Inline.t) : result Inline.t :=
  match c with
  | ISkip _ => ok c
  | IVardecl _ _ _ => ok c
  | IAssign type lhs rhs i =>
    match type with
    | E.THeader fields =>
      header_elaboration_assign i lhs rhs fields
    | _ => ok c
    end
  | IConditional guard_type guard tru fls i =>
  (** TODO: elaborate headers in guard? *)
  let* tru' := elaborate_headers tru in
  let+ fls' := elaborate_headers fls in
  IConditional guard_type guard tru' fls' i
| ISeq s1 s2 i =>
  let* s1' := elaborate_headers s1 in
  let+ s2' := elaborate_headers s2 in
  ISeq s1' s2' i

| IBlock b =>
  let+ b' := elaborate_headers b in
  IBlock b'
| IReturnVoid _ => ok c
| IReturnFruit _ _ _ => ok c
| IExit _ => ok c
| IInvoke x keys actions i =>
  let opt_actions := map_snd elaborate_headers actions in
  let+ actions' := rred (List.map res_snd opt_actions) in
  IInvoke x keys actions' i
| IExternMethodCall extern method arrow tags =>
  let arrow := elaborate_arrowE arrow in
  ok (IExternMethodCall extern method arrow tags)
| ISetValidity _ _ _ =>
  (* TODO Do we need to eliminate tuples in valid-sets? that seems ill-typed *)
  ok c
| IHeaderStackOp _ _ _ _ _ =>
  (* TODO Do we need to eliminate tuples in valid-sets? that seems ill-typed *)
  ok c
end.

Fixpoint ifold {A : Type} (n : nat) (f : nat -> A -> A) (init : A) :=
  match n with
  | O => init
  | S n' => f n (ifold n' f init)
  end.

Search (nat -> positive).

Definition extract_next extern fields (num : positive) hdr hs (tags:tags_t) : Inline.t :=
  let t := E.THeader fields in
  let extract arrow := IExternMethodCall extern "extract" arrow tags in
  let hdr_elem idx := E.EHeaderStackAccess fields hs (BinIntDef.Z.of_nat idx) tags in
  let valid i := E.EUop E.TBool E.IsValid (hdr_elem i) tags in
  let invalid i := E.EUop E.TBool E.Not (valid i) tags in
  let and a b := E.EBop E.TBool E.And a b tags in
  let lst := E.EExprMember t "last" hs tags in
  let arrow i := elaborate_arrowE ({| paramargs := [(hdr, PAOut (hdr_elem i))]; rtrns := None |}) in
  let ift b c := IConditional E.TBool b c (ISkip tags) tags in
  let next_and_last i :=
      (ISeq (extract (arrow i))
            (IAssign t lst (hdr_elem i) tags)
            tags) in
  ifold (BinPosDef.Pos.to_nat (BinPosDef.Pos.pred num))
        (fun i acc => ISeq acc
                           (ift (and (valid i) (invalid (i-1)))
                                (next_and_last i))
                           tags)
        (ift (invalid 0) (next_and_last 0)).

Definition elaborate_extract extern (arrow : E.arrowE tags_t) (tags : tags_t) : result Inline.t :=
  match arrow.(paramargs) with
  | [(hdr, (PAOut arg))] =>
    match arg with
    | E.EExprMember (E.THeaderStack fields num) mem header_stack tags =>
      if String.eqb mem "next"
      then ok (extract_next extern fields num hdr header_stack tags)
      else let arrow := elaborate_arrowE arrow in
           ok (IExternMethodCall extern "extract" arrow tags)
    | _ =>
      let arrow := elaborate_arrowE arrow in
      ok (IExternMethodCall extern "extract" arrow tags)
    end
  | _ =>
    let arrow := elaborate_arrowE arrow in
    ok (IExternMethodCall extern "extract" arrow tags)
  end.

Fixpoint elaborate_header_stacks (c : Inline.t) : result Inline.t :=
  match c with
  | ISkip _ => ok c
  | IVardecl type x i =>
    match type with
    | E.THeaderStack fields size =>
      ok (ifold (BinPos.Pos.to_nat size)
                (fun n acc => ISeq (IVardecl (E.THeader fields) (index_array_str x n) i) acc i) (ISkip i))
    | _ => ok c
    end
  | IAssign type lhs rhs i =>
    match type with
    | E.THeaderStack fields size =>
      match lhs, rhs with
      | E.EVar ltyp lvar il, E.EVar rtyp rvar ir =>
        let iter := ifold (BinPos.Pos.to_nat size) in
        (* Should these be `HeaderStackAccess`es? *)
        let lvars := iter (fun n => cons (index_array_str lvar n)) [] in
        let rvars := iter (fun n => cons (index_array_str rvar n)) [] in
        let+ lrvars := zip lvars rvars in
        let htype := E.THeader fields in
        let mk := E.EVar htype in
        fold_right (fun '(lv, rv) acc => ISeq (IAssign htype (mk lv il) (mk lv ir) i) acc i) (ISkip i) lrvars
      | _, _ =>
        (* Don't know how to translate anything but variables *)
        error "Tried to elaborate a header stack assignment that wasn't variables"
      end
    | _ => ok c
    end
  | IConditional gtyp guard tru fls i =>
    (* TODO Eliminate header stack literals from expressions *)
    let* tru' := elaborate_header_stacks tru in
    let+ fls' := elaborate_header_stacks fls in
    IConditional gtyp guard tru' fls' i

  | ISeq c1 c2 i =>
    let* c1' := elaborate_header_stacks c1 in
    let+ c2' := elaborate_header_stacks c2 in
    ISeq c1' c2' i

  | IBlock c =>
    let+ c' := elaborate_header_stacks c in
    IBlock c'

  | IReturnVoid _ => ok c
  | IReturnFruit _ _ _ => ok c
  | IExit _ => ok c
  | IInvoke x keys actions i =>
    (* TODO: Do something with keys? *)
    let rec_act_call := fun acc_opt '(nm, act) =>
        let* acc := acc_opt in
        let+ act' := elaborate_header_stacks act in
        (nm, act') :: acc
    in
    let+ actions' := fold_left rec_act_call actions (ok []) in
    IInvoke x keys (rev actions') i
  | IExternMethodCall extern method arrow tags =>
    if String.eqb method "extract"
    then elaborate_extract extern arrow tags
    else let arrow := elaborate_arrowE arrow in
         ok (IExternMethodCall extern method arrow tags)
  | ISetValidity _ _ _ =>
    (* TODO Eliminate header stack literals from expressions *)
    ok c
  | IHeaderStackOp stck typ ST.HSPush n tags =>
    let seq := fun hidx lodx => ISeq hidx lodx tags in
    let indexed_stck := index_array_str stck in
    let mk_ith_stack_copy :=
        fun i => IAssign typ
                         (E.EVar typ (indexed_stck i) tags)
                         (E.EVar typ (indexed_stck (i-1)) tags)
                         tags
    in
    ok (ifold (BinPos.Pos.to_nat n - 2) (fun i => seq (mk_ith_stack_copy (i+1)))
              (ISetValidity (E.EVar typ (indexed_stck 0) tags) true tags))
  | IHeaderStackOp stck typ ST.HSPop n tags =>
    let seq := fun hidx lodx => ISeq lodx hidx tags in
    let indexed_stck := index_array_str stck in
    let mk_ith_stack_copy :=
        fun i => IAssign typ
                         (E.EVar typ (indexed_stck i) tags)
                         (E.EVar typ (indexed_stck (i+1)) tags)
                         tags
    in
    let n := BinPos.Pos.to_nat n in
    ok (ifold (n - 2) (fun i => seq (mk_ith_stack_copy i))
              (ISetValidity (E.EVar typ (indexed_stck (n-1)) tags) true tags))
  end.

Fixpoint struct_fields (s : string) (fields : F.fs string E.t) : list (string * E.t)  :=
  F.fold (fun f typ acc => (s ++ "." ++ f, typ) :: acc ) fields [].

(** TODO: Compiler pass to elaborate structs *)
Fixpoint elaborate_structs (c : Inline.t) : result Inline.t :=
  match c with
  | ISkip _ => ok c
  | IVardecl type s i =>
    match type with
    | E.TStruct fields =>
      let vars := struct_fields s fields in
      let elabd_hdr_decls := fold_left (fun acc '(var_str, var_typ) => ISeq (IVardecl var_typ var_str i) acc i) vars (ISkip i) in
      ok elabd_hdr_decls
    | _ => ok c
    end
  | IAssign type lhs rhs i =>
    match type with
    | E.TStruct fields =>
      (** TODO : What other assignments to headers are legal? EHeader? EStruct? *)
      match lhs, rhs with
      | E.EVar _ l il, E.EVar _ r ir =>
        let lvars := struct_fields l fields in
        let rvars := struct_fields r fields in
        let+ lrvars := zip lvars rvars in
        fold_right (fun '((lvar, ltyp),(rvar, rtyp)) acc => ISeq (IAssign ltyp (E.EVar ltyp lvar il) (E.EVar rtyp rvar ir) i) acc i) (ISkip i) lrvars
      | E.EVar _ l il, E.EStruct explicit_fields i =>
        let lvars := struct_fields l fields in
        let assign_fields := fun '(lvar, ltyp) acc_opt =>
             let* acc := acc_opt in
             let*~ rval := F.find_value (String.eqb lvar) explicit_fields else "couldnt find field name in struct literal "in
             ok (ISeq (IAssign ltyp (E.EVar ltyp lvar il) rval i) acc i) in
        fold_right assign_fields
           (ok (ISkip i))
           lvars
      | _, _ =>
         error "Can only elaborate struct assignments of the form var := {var | struct literal}"
      end
    | _ => ok c
  end
  | IConditional guard_type guard tru fls i =>
    (** TODO: elaborate headers in guard? *)
    let* tru' := elaborate_structs tru in
    let+ fls' := elaborate_structs fls in
    IConditional guard_type guard tru' fls' i
  | ISeq s1 s2 i =>
    let* s1' := elaborate_structs s1 in
    let+ s2' := elaborate_structs s2 in
    ISeq s1' s2' i

  | IBlock b =>
    let+ b' := elaborate_structs b in
    IBlock b'
  | IReturnVoid _ => ok c
  | IReturnFruit _ _ _ => ok c
  | IExit _ => ok c
  | IInvoke x keys actions i =>
    let opt_actions := map_snd elaborate_structs actions in
    let+ actions' := rred (List.map res_snd opt_actions) in
    IInvoke x keys actions' i
  | IExternMethodCall extern method arrow tags =>
    let arrow := elaborate_arrowE arrow in
    ok (IExternMethodCall extern method arrow tags)
  | ISetValidity _ _ _ =>
    (* TODO Elaborate header stacks in expressions *)
    ok c
  | IHeaderStackOp _ _ _ _ _ =>
    ok c
end.

Fixpoint eliminate_slice_assignments (c : t) : result t :=
  match c with
  | ISkip _ => ok c
  | IVardecl _ _ _=> ok c
  | IAssign typ (E.ESlice e hi lo _) rhs i =>
    let lhs_typ := t_of_e e in
    let concat := fun typ lhs rhs => E.EBop typ E.PlusPlus lhs rhs i in
    let mk_new_rhs : positive -> E.e tags_t := fun w =>
      let upper := E.ESlice e w (BinPos.Pos.succ hi) i in
      let lower := E.ESlice e (BinPos.Pos.pred lo) (pos 0) i in
      let mid_type := E.TBit (Npos (BinPos.Pos.sub w lo)) in
      concat lhs_typ (concat mid_type upper rhs) lower in
    let* (rhs' : E.e tags_t) := match lhs_typ with
                 | E.TBit w => ok (mk_new_rhs (posN w))
                 | E.TInt w => ok (mk_new_rhs w)
                 | _ => error "Cannot get width"
                                end in
    ok (IAssign lhs_typ e rhs' i)
  | IAssign _ _ _ i => ok c
  | IConditional typ guard tru fls i =>
    let* tru' := eliminate_slice_assignments tru in
    let+ fls' := eliminate_slice_assignments fls in
    IConditional typ guard tru' fls' i
  | ISeq s1 s2 i =>
    let* s1' := eliminate_slice_assignments s1 in
    let+ s2' := eliminate_slice_assignments s2 in
    ISeq s1 s2 i
  | IBlock blk =>
    let+ blk' := eliminate_slice_assignments blk in
    IBlock blk'
  | IReturnVoid _ => ok c
  | IReturnFruit _ _ _ => ok c
  | IExit _ => ok c
  | IInvoke tbl keys actions i =>
    let+ actions' := F.fold (fun name act acts =>
             let* act' := eliminate_slice_assignments act in
             let+ acts' := acts in
             (name, act') :: acts') actions (ok []) in
    IInvoke tbl keys actions' i
  | ISetValidity  _ _ _  => ok c
  | IHeaderStackOp _ _ _ _ _ => ok c
  | IExternMethodCall _ _ _ _ => ok c
  end.

Definition inline_assert (check : E.e tags_t) (tags : tags_t) : t :=
  let args := {|paramargs := [("check", PAIn check)]; rtrns:= None|} in
  IExternMethodCall "_" "assert" args tags.

Definition isValid (hdr : E.e tags_t) (tags: tags_t) : E.e tags_t :=
  E.EUop E.TBool E.IsValid hdr tags.

(*inline_assert (isValid e tags) tags*)
Fixpoint header_asserts (e : E.e tags_t) (tags : tags_t) : result (list (E.e tags_t)) :=
  match e with
  | E.EBool _ _ | E.EBit _ _ _
  | E.EInt _ _ _ | E.EVar _ _ _
  | E.EError _ _ (*| E.EMatchKind _ _ *) =>  ok []
  | E.EExprMember type name e tags =>
    if String.eqb name "is_valid" then ok [] else
    match t_of_e e with
    | E.THeader _  =>
      ok [e]
    | _ =>
      ok []
    end
  | E.ESlice e _ _ tags =>
    header_asserts e tags
  | E.ECast _ e tags =>
    header_asserts e tags
  | E.EUop _ E.IsValid e tags =>
    ok []
  | E.EUop _ _ e tags =>
    header_asserts e tags
  | E.EBop _ _ lhs rhs tags =>
    let* lhs_asserts := header_asserts lhs tags in
    let* rhs_asserts := header_asserts rhs tags in
    ok (List.app lhs_asserts rhs_asserts)
  | E.ETuple _ _ =>
    (* List.fold_left (fun acc_asserts e => *)
    (* let* acc_asserts := acc_asserts in *)
    (* let+ new_asserts := header_asserts e tags in *)
    (* ISeq acc_asserts new_asserts tags) es (ok (ISkip tags)) *)
    error "[ERROR] [header_asserts] tuples should be factored out by now"
  | E.EStruct _ _ =>
    error "[ERROR] [header_asserts] structs should be factored out by now"
  | E.EHeader _ _ _ =>
    error "[ERROR] [header_asserts] header literals should be factored out by now"
  | E.EHeaderStack _ _ _ _ =>
    error "[ERROR] [header_asserts] header stacks should be factored out by now"
  | E.EHeaderStackAccess _ _ _ _ =>
    error "[ERROR] [header_asserts] header stack accesses should be factored out by now"
  end.


Definition get_from_paramarg {A : Type} (pa : paramarg A A) :=
  match pa with
  | PAIn a => a
  | PAOut a => a
  | PAInOut a => a
  | PADirLess a => a
  end.
Fixpoint assert_headers_valid_before_use (c : t) : result t :=
  let uniquify := ListUtil.uniquify ExprEquivalence.eqbe in
  let assertify hdrs tags :=
      List.fold_right (fun hdr cmd => ISeq (inline_assert (isValid hdr tags) tags) cmd tags)
                      (ISkip tags)
                      (uniquify hdrs)
  in
  match c with
  | ISkip _
  | IVardecl _ _ _=> ok c
  | IAssign _ lhs rhs tags =>
    let* lhs_asserts := header_asserts lhs tags in
    let+ rhs_asserts := header_asserts rhs tags in
    let asserts := assertify (List.app lhs_asserts rhs_asserts) tags in
    ISeq asserts c tags
  | IConditional typ guard tru fls tags =>
    let* tru' := assert_headers_valid_before_use tru in
    let* fls' := assert_headers_valid_before_use fls in
    let+ guard_headers := header_asserts guard tags in
    let  guard_asserts := assertify guard_headers tags in
    ISeq guard_asserts (IConditional typ guard tru' fls' tags) tags
  | ISeq s1 s2 tags =>
    let* s1' := assert_headers_valid_before_use s1 in
    let+ s2' := assert_headers_valid_before_use s2 in
    ISeq s1' s2' tags
  | IBlock blk =>
    let+ blk' := assert_headers_valid_before_use blk in
    IBlock blk'
  | IReturnVoid _ => ok c
  | IReturnFruit _ e tags =>
    let+ headers := header_asserts e tags in
    let  asserts := assertify headers tags in
    ISeq asserts c tags
  | IExit _ => ok c
  | IInvoke t ks acts tags =>
  (* Assume keys have been normalized, so dont to check them*)
    let+ acts' := rred (List.map (fun '(a,c) =>
                  let+ c' := assert_headers_valid_before_use c in
                  (a, c')) acts) in
    IInvoke t ks acts' tags
  | ISetValidity  _ _ _  => ok c
  | IHeaderStackOp _ _ _ _ _ =>
    (* Assume this has been factored out already *)
    error "header stacks should have been factored out already"
  | IExternMethodCall ext method args tags =>
    if String.eqb method "extract" then ok c else
    let paramargs := paramargs args in
    let+ headers := List.fold_left (fun acc_hdrs '(param, arg)  =>
                   let* acc_hdrs := acc_hdrs in
                   let arg_exp := get_from_paramarg arg in
                   let+ new_hdrs := header_asserts arg_exp tags in
                   List.app acc_hdrs new_hdrs) paramargs (ok []) in
    let  asserts := assertify headers tags in
    ISeq asserts (IExternMethodCall ext method args tags) tags
  end.

End Inline.
