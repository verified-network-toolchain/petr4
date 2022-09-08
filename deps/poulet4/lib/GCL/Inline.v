From Coq Require Import Program.Basics Arith.EqNat String List NArith.BinNat.
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
Module F := Field.

Section Inline.
Variable tags_t : Type.
  
(* this needs to be changed to an array access *)
(*Left and right brackets for array accesses *)
Definition AAL := "$_". (* evoke [ *)
Definition AAR := "_$". (* evoke ] *)
Definition index_array_str s idx :=
  s ++ AAL ++ string_of_nat idx ++ AAR.

Definition expenv : Type := Env.t string E.e.

Definition get_exp (pa : paramarg E.e E.e) :=
  match pa with
  | PAInOut e => e
  | PAIn e => e
  | PAOut e => e
  end.

Definition args_to_expenv (args : F.fs string (paramarg E.e E.e)) : expenv :=
  List.fold_right (fun '(param,arg) (env : expenv) => Env.bind param (get_exp arg) env) [] args.

Fixpoint subst_e (η : expenv) (e : E.e) : E.e :=
  match e with
  | E.Bool _ => e
  | E.Bit _ _ => e
  | E.Int _ _ => e
  | E.Var _ og _ =>
    match Env.find og η with
    | None => e
    | Some e' => e'
    end
  | E.Slice hi lo e =>
    E.Slice hi lo (subst_e η e)
  | E.Cast type arg =>
    E.Cast type (subst_e η arg)
  | E.Uop op type arg =>
    E.Uop op type (subst_e η arg)
  | E.Bop t op l r =>
    E.Bop t op (subst_e η l) (subst_e η r)
  | E.Lists ls es =>
    E.Lists ls (List.map (subst_e η) es)
  | E.Member mem expr_type arg =>
    E.Member mem expr_type (subst_e η arg)
  | E.Error _ => e
  | E.Index t stack idx =>
    E.Index t (subst_e η stack) (subst_e η idx)
  end.

Inductive t : Type :=
| ISkip                        (* skip, useful for
                                               small-step semantics *)
| IVardecl (type : E.t)
           (x : string)     (* Variable declaration. *)
| IAssign (type : E.t) (lhs rhs : E.e)
                               (* assignment *)
| IConditional (guard_type : E.t)
               (guard : E.e)
               (tru_blk fls_blk : t)  (* conditionals *)
| ISeq (s1 s2 : t)                    (* sequences *)
| IBlock (blk : t)                                (* blocks *)
| IReturnVoid                         (* void return statement *)
| IReturnFruit (t : E.t)
               (e : E.e)       (* fruitful return statement *)
| IExit                               (* exit statement *)
| IInvoke (x : string)
          (keys : list (E.t * E.e * string))
          (actions : list (string * t))
| IExternMethodCall (extn : string) (method : string)
    (args : F.fs string (paramarg E.e E.e)) (ret : option Expr.e).

Definition assume b  :=
  IExternMethodCall "_" "assume" [("check",PAIn b)] None .

Definition rename_string (table action x : string) (params : list string) :=
  if fold_right (fun y => orb (String.eqb x y)) false params
  then "_symb$" ++ table ++ "$" ++ action ++ "$arg$" ++ x
  else x.

Fixpoint action_param_renamer_expr (table action : string) (params : list string) (e : E.e) : E.e :=
  match e with
  | E.Bool _ => e
  | E.Bit _ _ => e
  | E.Int _ _ => e
  | E.Var type og x =>
    E.Var type (rename_string table action og params) x
  | E.Slice hi lo e =>
    E.Slice hi lo (action_param_renamer_expr table action params e)
  | E.Cast typ arg =>
    E.Cast typ (action_param_renamer_expr table action params arg)
  | E.Uop op typ arg =>
    E.Uop op typ (action_param_renamer_expr table action params arg)
  | E.Bop t op le re =>
    let le' := action_param_renamer_expr table action params le in
    let re' := action_param_renamer_expr table action params re in
    E.Bop t op le re
  | E.Lists ls es =>
    E.Lists ls (List.map (action_param_renamer_expr table action params) es)
  | E.Member mem expr_type arg =>
      E.Member mem expr_type (action_param_renamer_expr table action params arg)
  | E.Index t e1 e2 =>
      E.Index
        t (action_param_renamer_expr table action params e1)
        (action_param_renamer_expr table action params e2)
  | E.Error _ => e
  end.

Fixpoint action_param_renamer (table action : string) (params : list string) (c : t) : result string (t * list string) :=
  match c with
  | ISkip => ok (c, params)
  | IVardecl type x =>
      ok (c, filter (negb ∘ (String.eqb x)) params)
  | IAssign t lhs rhs =>
    let rhs' := action_param_renamer_expr table action params rhs in
    let lhs' := action_param_renamer_expr table action params lhs in
    ok (IAssign t lhs' rhs', params)
  | IConditional typ cond tru fls =>
    let cond' := action_param_renamer_expr table action params cond in
    let* (tru', _) := action_param_renamer table action params tru in
    let+ (fls', _) := action_param_renamer table action params fls in
    (IConditional typ cond' tru' fls', params)
  | ISeq c1 c2 =>
    let* (c1', params1) := action_param_renamer table action params c1 in
    let+ (c2', params2) := action_param_renamer table action params1 c2 in
    (ISeq c1' c2', params2)
  | IBlock blck =>
    let+ (blck', _) := action_param_renamer table action params blck in
    (blck', params)
  | IReturnVoid => ok (c, params)
  | IReturnFruit t e =>
    let e' := action_param_renamer_expr table action params e in
    ok (IReturnFruit t e', params)
  | IExit => ok (c, params)
  | IInvoke _ _ _ =>
    error "Invocations should not occur within actions"
  | IExternMethodCall extn method pargs ret =>
      let pargs' :=
        F.map (paramarg_map_same (action_param_renamer_expr table action params)) pargs in
      ok (IExternMethodCall extn method pargs' ret, params)
  end.

Fixpoint subst_t (η : expenv) (c : t) : (t * expenv) :=
  match c with
  | ISkip => (ISkip, η)
  | IVardecl type x =>
      (IVardecl type x, Env.remove x η)
  | IAssign t lhs rhs =>
    (IAssign t (subst_e η lhs) (subst_e η rhs), η)
  | IConditional guard_type guard tru_blk fls_blk =>
    (IConditional guard_type
                  (subst_e η guard)
                  (fst (subst_t η tru_blk))
                  (fst (subst_t η fls_blk))
                 , η)
  | ISeq s1 s2 =>
    let (s1', η1) := subst_t η s1 in
    let (s2', η2) := subst_t η1 s2 in
    (ISeq s1' s2', η2)
  | IBlock blk =>
    (IBlock (fst (subst_t η blk)), η)
  | IReturnVoid => (c, η)
  | IReturnFruit t e => (IReturnFruit t (subst_e η e),η)
  | IExit => (c,η)
  | IInvoke x keys actions =>
    let keys' := List.map (fun '(t, m,k) => (t, subst_e η m, k)) keys in
    let actions' := List.map (fun '(s,a) => (s, fst(subst_t η a))) actions in
    (IInvoke x keys' actions', η)

  | IExternMethodCall extn method pas returns =>
    let pas' := F.map (paramarg_map (subst_e η) (subst_e η)) pas in
    (IExternMethodCall extn method pas' returns, η)
  end.

Definition copy (args : list (string * paramarg E.e E.e)) : expenv :=
  List.fold_right (fun '(param,arg) η => match arg with
                             | PAIn e => Env.bind param e η
                             | PAInOut e => Env.bind param e η
                             | PAOut e => Env.bind param e η
                             end)
         (Env.empty String.string E.e) args.

Definition string_list_of_params (ps : E.params) : list string :=
  List.map fst ps.

Fixpoint elaborate_arg_expression (param : string) (arg : E.e) : F.fs string E.e :=
  let access := fun s f => s ++ "." ++ f in
  let is_valid :=
    let one_bit := E.TBool in
    (access param "is_valid",
      E.Uop one_bit E.IsValid arg) in
  let member_member := fun f t => E.Member t f arg in
  let loop := fun idx t acc => (access param (string_of_nat idx), member_member idx t) :: acc in
  match arg with
  | E.Var (E.TStruct false fs) og x =>
      ListUtil.fold_righti loop [] fs
  | E.Var (E.TStruct true fs) _ _ =>
      ListUtil.fold_righti loop [is_valid] fs
  | E.Member (E.TStruct false fs) mem _ =>
      ListUtil.fold_righti loop [] fs
  | E.Member (E.TStruct true fs) mem _ =>
      ListUtil.fold_righti loop [is_valid] fs
  | E.Var (E.TArray size t) og x =>
      List.map
        (fun idx => (index_array_str param idx, (E.Var t (index_array_str og idx) x))) (seq 0 (N.to_nat size))
  | E.Lists (E.lists_array _) es =>
      ListUtil.fold_righti (fun i e acc =>
          let param_i := index_array_str param i in
          let es := elaborate_arg_expression param_i e in
          List.app es acc) [] es
  | E.Index t stk idx => [(param, arg)] (* TODO: get length from type of stk & iterate *)
  | E.Var (E.TVar _) _ _ => [(param, arg)]
  | _ => [(param, arg)]
  end.

Definition paramarg_map_union {A B : Set} (f : A -> F.fs string B) (pa : paramarg A A) : F.fs string (paramarg B B) :=
  match pa with
  | PAIn a => F.map PAIn (f a)
  | PAOut a => F.map PAOut (f a)
  | PAInOut a => F.map PAInOut (f a)
  end.

Definition elaborate_argument (parg : F.f string (paramarg E.e E.e)) : F.fs string (paramarg E.e E.e) :=
  let '(param, arg) := parg in
  paramarg_map_union (elaborate_arg_expression param) arg.


Definition elaborate_arguments (args : F.fs string (paramarg E.e E.e)) :  F.fs string (paramarg E.e E.e) :=
  List.concat (List.map elaborate_argument args).

Definition realize_symbolic_key (symb_var : string) (key_type : E.t) (key : E.e) (mk : string) :=
  let symb_key := E.Var key_type symb_var 0 in (* TODO: what de bruijn var to use? *)
  let eq_cond := E.Bop E.TBool E.Eq symb_key key in
  if (mk =? "exact")%string then
    (symb_key, eq_cond, E.Bool false)
  else
    (symb_key, eq_cond, E.Var E.TBool (symb_var ++ "$DONTCARE") 0) (* TODO: what de bruijn var to use? *).

Fixpoint normalize_keys_aux t (keys : list (E.t * E.e * string)) i  :=
  let keyname := "_symb$" ++ t ++ "$match_" ++ string_of_nat i in
  match keys with
  | [] => (ISkip , [])
  | ((key_type, key_expr, key_mk)::keys) =>
    let (assumes, new_keys) := normalize_keys_aux t keys (i+1)  in
    let '(symb_key, eq, skip_eq) := realize_symbolic_key keyname key_type key_expr key_mk in
    let new_assume := IConditional E.TBool skip_eq (ISkip ) (assume eq )  in
    (ISeq new_assume assumes , (key_type, symb_key, key_mk)::new_keys)
  end.

Definition normalize_keys t keys := normalize_keys_aux t keys 0.

Definition get_state_name state :=
  match state with
  | Parser.Start => "start"
  | Parser.Accept => "accept"
  | Parser.Reject => "reject"
  | Parser.Name s => string_of_nat s
  end.

Definition state_flag_name name := "_state$" ++ name ++ "$next".
Definition state_flag name : E.e := E.Var E.TBool (state_flag_name name) 0. (* TODO what de bruijn vars to use. *)
Definition set_state_flag name value  := IAssign E.TBool (state_flag name) (E.Bool value) .
Definition construct_state name stmt trans :=
  IConditional E.TBool
               (state_flag name)
               (ISeq (set_state_flag name false)
                     (ISeq stmt trans))
               ISkip.

Definition extract_single (es : list E.e) (msg : string) : result string E.e :=
  match es with
  | [e] => ok e
  | _ => error msg
  end.

Fixpoint elim_tuple_expr (e : E.e) :=
  match e with
  | E.Bool _
  | E.Bit _ _
  | E.Int _ _ => ok [e]
  | E.Var _ _ _ =>
    (* TODO a var can (?) be a tuple, need to inline it here. *)
    ok [e]
  | E.Slice _ _ _ =>
    (* A tuple cannot be sliced *)
    ok [e]
  | E.Cast t e =>
    let* es := elim_tuple_expr e in
    let+ e := extract_single es "TypeError: tuples cannot be cast" in
    [E.Cast t e]
  | E.Uop t op e =>
    (* THere are no unary operations that operate on Tuples *)
    let* es := elim_tuple_expr e in
    let+ e := extract_single es "TypeError: no unary operators for tuples" in
    [E.Uop t op e]
  | E.Bop t op e e' =>
    match op with
    | E.Eq =>
      let* es  := elim_tuple_expr e in
      let* es' := elim_tuple_expr e' in
      let+ eq_pairs := zip es es' in
      let eq := fun e1 e2 => E.Bop E.TBool E.Eq e1 e2 in
      let and := fun e1 e2 => E.Bop E.TBool E.And e1 e2 in
      [fold_right (fun '(e1,e2) => and (eq e1 e2))
                  (E.Bool true)
                  eq_pairs]
    | _ =>
      let* es  := elim_tuple_expr e in
      let* es' := elim_tuple_expr e' in
      let* e := extract_single es "TypeError: (=) is the only binary op on tuples got something else" in
      let+ e' := extract_single es' "TypeError: (=) is the only binary op on tuples got something else" in
      [E.Bop t op e e']
    end
  | E.Lists _ es =>
    let+ ees := rred (List.map elim_tuple_expr es) in
    List.concat ees
  | _ =>
  (* TODO Figure out what to do more complicated types *)
    ok [e]
  end.


Definition translate_simple_patterns pat : result string E.e :=
  match pat with
  | Parser.Bit w v =>
    ok (E.Bit w v)
  | Parser.Int w v =>
    ok (E.Int w v)
  | _ =>
    error "pattern too complicated, expecting int or bv literal"
  end.




Program Fixpoint translate_pat e pat { struct pat } : result string E.e  :=
  let bool_op := fun o x y => E.Bop E.TBool o x y in
  let mask := fun t x y => E.Bop t E.BitAnd x y in
  let and := bool_op E.And in
  let eq := bool_op E.Eq in
  let le := bool_op E.Le in
  match pat with
  | Parser.Wild =>
    ok (E.Bool true)
  | Parser.Mask pat msk =>
    let* e_pat := translate_simple_patterns pat in
    let+ e_msk := translate_simple_patterns msk in
    let t := t_of_e e_pat in
    eq (mask t e e_msk) (mask t e_pat e_msk)
  | Parser.Range lo hi =>
    let* e_lo := translate_simple_patterns lo in
    let+ e_hi := translate_simple_patterns hi in
    and (le e e_hi)
        (le e_lo e)
  | Parser.Bit _ _
  | Parser.Int _ _ =>
    let+ e_pat := translate_simple_patterns pat in
    eq e e_pat
  | Parser.Lists pats =>
    let* es := elim_tuple_expr e in
    let+ matches :=
       ListUtil.fold_lefti
       (fun i p acc => let* acc := acc in
                       let* e := ListUtil.ith es i in
                       let+ cond := translate_pat e p in
                       and acc cond)
       (ok (E.Bool true)) pats
    in
    matches
  end.

Definition lookup_parser_state name states : option Stmt.s :=
  Field.get name (List.combine (List.map string_of_nat (seq 0 (List.length states))) states).

Definition lookup_parser_states (names : list string) states :=
  List.fold_right
    (fun n acc =>
       match lookup_parser_state n states with
       | None => acc
       | Some s => (n,s) :: acc
       end) [] names.

Definition init_parser (states : list string) :=
  List.fold_right (fun f acc => if String.eqb f "start"
                         then ISeq (set_state_flag f true ) acc 
                         else ISeq (set_state_flag f false ) acc )
    (ISeq (set_state_flag "accept" false ) (set_state_flag "reject" false )) states.

Open Scope list_scope.

Fixpoint inline_transition (gas : nat)
                       (unroll : nat)
                       (ctx : DeclCtx)
                       (name : string)
                       (trans : Parser.pt)
  : result string ((list string) * t)  :=
       match gas with
       | O => ok ([], ISkip )
       | S gas =>
         match trans with
         | Parser.Direct state  =>
           let name := get_state_name state in
           ok ([name], set_state_flag name true )
         | Parser.Select discriminee default states  =>
           let default := inline_transition gas unroll ctx name (Parser.Direct default)  in
           let inline_trans_loop := fun '(pat, trans) acc  =>
                    let* (states, inln) := acc in
                    let* cond := translate_pat  discriminee pat in
                    let+ (new_states, trans) := inline_transition gas unroll ctx name (Parser.Direct trans) in
                    (states ++ new_states, IConditional E.TBool cond trans inln ) in
           List.fold_right inline_trans_loop default states
         end
       end.

Fixpoint transition_of_state (s : Stmt.s) : result Parser.trns :=
  match s with
  | Stmt.Var _ _ s => transition_of_state s
  | Stmt.Seq _ s => transition_of_state s
  | Stmt.Transition pt => ok pt
  | _ => error "no parser transition"
  end.

(*Fixpoint has_typ_var (t : E.t) : bool :=
  match t with
  | E.TVar _ => true
  | E.TBool
  | E.TBit _
  | E.TInt _
  | E.TError => false
  | E.TArray _ t => has_typ_var t
  | E.TStruct _ ts => List.existsb has_typ_var ts
  end.*)

(*Fixpoint e_has_typ_var (e : E.e) : bool :=
  match e with
  | E.Bool _
  | E.Bit _ _
  | E.Int _ _
  | E.Error _ => false
  | E.Var t _ _ => has_typ_var t
  | E.Slice _ _ e => e_has_typ_var e
  | E.Cast t e
  | E.Uop t _ e
  | E.Member t _ e => has_typ_var t || e_has_typ_var e
  | E.Bop t _ e₁ e₂
  | E.Index t e₁ e₂ => has_typ_var t || e_has_typ_var e₁ || e_has_typ_var e₂
  | E.Lists (E.lists_array t) es => has_typ_var t || List.existsb e_has_typ_var es
  | E.Lists _ es => List.existsb e_has_typ_var es
  end.*)

(*Definition p_has_typ_var (p : Parser.trns) : bool :=
  match p with
  | Parser.Direct _ => false
  | Parser.Select e _ _ => e_has_typ_var e
  end.*)

(*Definition funkind_has_typ_var (fk : ST.fun_kind) : bool :=
  match fk with
  | ST.Method _ _ ts None
  | ST.Funct _ ts None => List.existsb has_typ_var ts
  | ST.Method _ _ ts (Some e)
  | ST.Funct _ ts (Some e) => e_has_typ_var e || List.existsb has_typ_var ts
  | ST.Action _ es => List.existsb e_has_typ_var es
  end.*)

(*Fixpoint s_has_typ_var (s : ST.s) : bool :=
  match s with
  | ST.Skip
  | ST.Exit
  | ST.Invoke _
  | ST.Return None => false
  | ST.Return (Some e) => e_has_typ_var e
  | ST.Transition e => p_has_typ_var e
  | ST.Assign e₁ e₂ => e_has_typ_var e₁ || e_has_typ_var e₂
  | ST.Call fk args =>
      funkind_has_typ_var fk
      || List.existsb e_has_typ_var (List.map paramarg_elim args)
  | ST.Apply _ _ args =>
      List.existsb e_has_typ_var (List.map paramarg_elim args)
  | ST.Var _ (inl t) s => has_typ_var t || s_has_typ_var s
  | ST.Var _ (inr e) s => e_has_typ_var e || s_has_typ_var s
  | ST.Seq s₁ s₂ => s_has_typ_var s₁ || s_has_typ_var s₂
  | ST.Conditional e s₁ s₂ =>
      e_has_typ_var e || s_has_typ_var s₁ || s_has_typ_var s₂
  end.*)

(*Fixpoint s_extern_has_typ_var (s : ST.s) : bool :=
  match s with
  | ST.Call _ args =>
      List.existsb e_has_typ_var (List.map paramarg_elim args)
  | ST.Var _ _ s => s_extern_has_typ_var s
  | ST.Conditional _ s₁ s₂
  | ST.Seq s₁ s₂ =>
      s_extern_has_typ_var s₁ || s_extern_has_typ_var s₂
  | _ => false
  end.*)

(*Fixpoint i_has_typ_var (i : t) : bool :=
  match i with
  | ISkip
  | IExit
  | IReturnVoid => false
  | IVardecl t _ => has_typ_var t
  | IReturnFruit t e => has_typ_var t || e_has_typ_var e
  | IAssign t e₁ e₂ =>
      has_typ_var t || e_has_typ_var e₁ || e_has_typ_var e₂
  | IConditional t e i₁ i₂ =>
      has_typ_var t || e_has_typ_var e
      || i_has_typ_var i₁ || i_has_typ_var i₂
  | ISeq i₁ i₂ => i_has_typ_var i₁ || i_has_typ_var i₂
  | IBlock i => i_has_typ_var i
  | IInvoke _ key tbl =>
      List.existsb (fun '(t,e,_) => has_typ_var t || e_has_typ_var e) key
      || List.existsb (i_has_typ_var ∘ snd) tbl
  | IExternMethodCall _ _ args None =>
      List.existsb e_has_typ_var (List.map (paramarg_elim ∘ snd) args)
  | IExternMethodCall _ _ args (Some e) =>
      e_has_typ_var e ||
        List.existsb e_has_typ_var (List.map (paramarg_elim ∘ snd) args)
  end.*)

(*Fixpoint i_extern_has_typ_var (i : t) : bool :=
  match i with
  | IConditional _ _ i₁ i₂
  | ISeq i₁ i₂ => i_extern_has_typ_var i₁ || i_extern_has_typ_var i₂
  | IBlock i => i_extern_has_typ_var i
  | IInvoke _ _ tbl =>
      List.existsb (i_extern_has_typ_var ∘ snd) tbl
  | IExternMethodCall _ _ args _ =>
      List.existsb e_has_typ_var (List.map (paramarg_elim ∘ snd) args)
  | _ => false
  end.*)

Fixpoint inline_state
         (gas : nat)
         (unroll : nat)
         (ctx : DeclCtx)
         (name : string)
         (state : Stmt.s)
         (states : list Stmt.s)
  : result string ((list (string * Stmt.s)) * t) :=
  match gas with
  | O => ok ([], ISkip )
  | S gas =>
    let* stmt := inline gas unroll ctx state in
    let* trns := transition_of_state state in
    let+ (neighbor_names, trans) := inline_transition gas unroll ctx name trns  in
    let neighbor_states := lookup_parser_states neighbor_names states in
    (neighbor_states, construct_state name stmt trans )
  end
with inline_parser (gas : nat)
                   (unroll : nat)   
                   (ctx : DeclCtx)
                   (current_name : string)
                   (current : Stmt.s)
                   (states : list Stmt.s)
     : result string t :=
       match gas with
       | O => ok ISkip
       | S gas =>
         let* (neighbors, inline_current) := inline_state gas unroll ctx current_name current states  in
         if orb (PeanoNat.Nat.eqb (length neighbors) 0) (PeanoNat.Nat.eqb unroll 0)
         then ok (inline_current)
         else List.fold_left (fun inln '(n, s) =>
               let* inln := inln in
               let+ prsr := inline_parser gas (unroll-1) ctx n s states in
               ISeq inln prsr) neighbors (ok inline_current)
       end
with inline (gas : nat)
            (unroll : nat)
            (ctx : DeclCtx)
            (s : ST.s)
  : result string t :=
  match gas with
  | O => error "Inliner ran out of gas"
  | S gas =>
    match s with
    | ST.Skip =>
      ok ISkip
    | ST.Var x t_or_e s =>
        let+ s := inline gas unroll ctx s in
        match t_or_e with
        | inl t =>  ISeq (IVardecl t x) s
        | inr e =>
            let t := t_of_e e in
            ISeq (IVardecl t x) (ISeq (IAssign t (E.Var t x 0) e) s)
        end
    | ST.Assign lhs rhs =>
      ok (IAssign (t_of_e rhs) lhs rhs)
    | ST.Conditional guard tru_blk fls_blk =>
      let* tru_blk' := inline gas unroll ctx tru_blk in
      let+ fls_blk' := inline gas unroll ctx fls_blk in
      IConditional (t_of_e guard) guard tru_blk' fls_blk'

    | ST.Seq s1 s2 =>
      let* i1 := inline gas unroll ctx s1 in
      let+ i2 := inline gas unroll ctx s2 in
      ISeq i1 i2

    | ST.Call (ST.Funct f _ ret) args =>
(*if List.existsb e_has_typ_var (List.map paramarg_elim args)
then error "args has typevar call funct" else  *)
      match find_function ctx f with
      | Some (TD.Funct _ _ {| paramargs:=params |} body) =>
          (*if s_extern_has_typ_var body then error "funct body has type var" else*)
        (** TODO check copy-in/copy-out *)
            let* rslt := inline gas unroll ctx body in
            (*if i_extern_has_typ_var rslt then error "funct rslt has type var" else*)
        let args := List.combine (List.map fst params) args in
        let (s,_) := subst_t (args_to_expenv args)
                       rslt in
        (*if i_extern_has_typ_var s then error "funct blk has type var" else*)
        ok $ IBlock s
      | Some _ =>
        error "[ERROR] Got a nonfunction when `find`ing a function"
      | None =>
          (* let args := elaborate_arguments args in
             ok (IExternMethodCall "_" f args ret) *)
          error
            ("[TODO] not sure what to do here... Could not find function " ++ f)
      end

    | ST.Call (ST.Action a ctrl_args) data_args =>
      let* adecl := from_opt (find_action ctx a) ("could not find action " ++ a ++ " in environment")%string in
      match adecl with
      | CD.Action _ ctrl_params data_params body =>
          (*if s_extern_has_typ_var body then
            error "body has type var" else*)
        (** TODO handle copy-in/copy-out *) (* TODO handle control args *)
        let data_args :=
          List.combine (List.map fst data_params) data_args in
        let ctrl_args :=
          List.combine (List.map fst ctrl_params) (List.map PAIn ctrl_args) in
        let* rslt := inline gas unroll ctx body in
        (*if i_extern_has_typ_var rslt then
          error "rslt has type var" else*)
        let η := args_to_expenv (ctrl_args ++ data_args) in
        let blk := fst (subst_t η rslt) in
        (*if i_extern_has_typ_var blk then
          error "action block has type var" else*)
        ok $ IBlock blk
      | _ =>
        error "[ERROR] got a nonaction when `find`-ing a function"
      end

    | ST.Apply inst ext_args args  =>
        (*if (inst =? "h'3")%string then error "where is it applying h3?" else*)
      match find_control ctx inst with
      | None =>
        let parser := find_parser ctx inst in
        let* pinst := from_opt parser ("could not find controller or parser named " ++ inst)%string in
        match pinst with
        | TD.Instantiate pname _ _ pargs expr_pargs  =>
          let pdecl_opt := find_parser ctx pname in
          let* pdecl := from_opt pdecl_opt ("could not find parser of type " ++ pname)%string in
          match pdecl with
          | TD.Parser _ _ _ _ _ start states  =>
            let+ parser := inline_parser gas unroll  ctx "start" start states in
            let init := init_parser ("start" :: List.map string_of_nat (seq 0 (List.length states)))  in
            ISeq init  parser 
          (* error ("found parser " ++ inst ++ " of type " ++ pname ++ " [TODO] translate the parser!") *)
          | _ =>
            error ("expected `" ++ pname ++ "` to be a parser declaration, but it was something else")%string
          end
        | _ =>
          error ("expected `" ++ inst ++ "` to be a instantiation, but it was something else")%string
        end
      | Some cinst =>
        match cinst with
        | TD.Instantiate cname iname _ cargs expr_cargs =>
          let cdecl_opt := find_control ctx cname in
          let* cdecl := from_opt cdecl_opt "could not find controller" in
          match cdecl with
          | TD.Control _ _ _ _ params body apply_blk =>
              (*if s_extern_has_typ_var apply_blk then error "apply_blk has type var" else*)
            (* Context is begin extended with body, but why can't I find the controls? *)
            let ctx' := List.fold_left of_cdecl body ctx in
            let* rslt := inline gas unroll ctx' apply_blk in
            (*if i_extern_has_typ_var rslt then error "control rslt has type var" else*)
              (** TODO check copy-in/copy-out *)
            (*if List.existsb e_has_typ_var (List.map paramarg_elim args)
              then error
                     ("control " ++ cname ++ " instance " ++ iname ++ " args has type var")%string
              else*)
            let args := List.combine (List.map fst params) args in
            let η := copy args in
            (*if List.existsb e_has_typ_var (List.map snd η)
            then error "control η has type var" else*)
            let blk := (fst (subst_t η rslt)) in
            (*if i_extern_has_typ_var blk then error "control blk as type var" else*)
            ok $ IBlock blk
          | _ =>
            error "Expected a control decl, got something else"
          end
        | _ =>
          error "Expected a control instantiation, got something else"
        end
      end
    | ST.Return None =>
      ok IReturnVoid

    | ST.Return (Some expr) =>
      ok (IReturnFruit (t_of_e expr) expr)

    | ST.Exit =>
      ok IExit

    | ST.Invoke tbl_name =>
      let* tdecl := from_opt (find_table ctx tbl_name) "could not find table in environment" in
      match tdecl with
      | CD.Table _ key actions =>
        let keys : list (E.t * E.e * string) :=
          List.map (fun '(e,m) => (t_of_e e,e,m)) key in
        let act_size := Nat.max (PeanoNat.Nat.log2_up (List.length actions)) 1 in
        let act_sizeN := BinNat.N.of_nat act_size in
        let act_type := E.TBit act_sizeN in
        let act_to_gcl := fun i a acc_res =>
          let* acc := acc_res in
          let* act := from_opt (find_action ctx a) ("could not find action " ++ a ++ " in environment")%string in
          match act with
          | CD.Action _ ctrl_params data_params body  =>
              (*if s_extern_has_typ_var body then error "tbl action body has typ var" else*)
                let* s := inline gas unroll ctx body in
                (*if i_extern_has_typ_var s then error "tbl s has typ var" else*)
            let* (s', _) :=
              action_param_renamer tbl_name a
                (List.map fst ctrl_params ++ string_list_of_params data_params) s in
            (*if i_extern_has_typ_var s' then error "tbl s' has type var" else*)
            let set_action_run :=
                IAssign act_type
                          (E.Var act_type ("_return$" ++ tbl_name ++ ".action_run") 0)
                          (E.Bit act_sizeN (BinInt.Z.of_nat i)) 
            in
            ok (ISeq set_action_run s' :: acc)
          | _ =>
            error "[ERROR] expecting action when `find`ing action, got something else"
          end
        in
        let* acts := fold_lefti act_to_gcl (ok []) (List.map fst actions) in
        let* named_acts := zip (List.map fst actions) acts in
        let (assumes, keys') := normalize_keys tbl_name keys in
        (*if i_extern_has_typ_var assumes then error "assumes has typ var" else*)
          let invocation := IInvoke tbl_name keys' named_acts in
          (*if i_extern_has_typ_var invocation then error "invocation has typ var" else*)
            ok $ ISeq assumes invocation
      | _ =>
        error "[ERROR] expecting table when getting table, got something else"
      end

    | ST.Call (ST.Method ext method _ ret) args =>
        (*if List.existsb e_has_typ_var (List.map paramarg_elim args)
            then error "args has typevar call method" else*)
        match find_extern ctx ext with
        | Some (TD.Extern _ _ _ _ methods) =>
            let* '((_, _, {|paramargs:=params|}) : nat * list string * Expr.arrowT) :=
              Result.from_opt
                (Field.get method methods)
                ("[Error] couldn't find extern method "
                   ++ method ++ " in extern " ++ ext) in
            (*if List.existsb e_has_typ_var (List.map paramarg_elim args)
            then error "args has typevar 1" else*)
              let args := List.combine (List.map fst params) args in
              (*if List.existsb e_has_typ_var (List.map (paramarg_elim ∘ snd) args)
            then error "args has typevar 2" else*)
            ok (IExternMethodCall ext method args ret)
        | _ => error
                ("[ERROR] expecting extern when getting extern, got something else for "
                   ++ ext ++ " & method " ++ method)
        end

    | ST.Transition _ =>  ok ISkip (*[TODO] how to hanlde parser transitions?*)
    end
  end.

Open Scope string_scope.
Definition seq_tuple_elem_assign
           (tuple_name : string)
           (n : nat)
           (p : E.t * E.e)
           (acc : Inline.t) : Inline.t :=
  let (t, e) := p in
  let tuple_elem_name := tuple_name ++ "__tup__" ++ string_of_nat n in
  let lhs := E.Var t tuple_elem_name 0 in
  Inline.ISeq (Inline.IAssign t lhs e) acc.

Definition elim_tuple_assign (ltyp : E.t) (lhs rhs : E.e) : result string Inline.t :=
  match lhs, rhs with
  | E.Var (E.TStruct false types) x _, E.Lists E.lists_struct es =>
    let+ te := zip types es in
    fold_lefti (seq_tuple_elem_assign x) (Inline.ISkip) te
  | _,_ => ok (Inline.IAssign ltyp lhs rhs)
  end.

Definition elaborate_tuple_literal
           (param : string)
           (ctor : E.e -> paramarg E.e E.e)
           (es : list E.e)
           (args : F.fs string (paramarg E.e E.e)) :=
  ListUtil.fold_righti (fun idx e acc =>
   let index := fun s =>  index_array_str s idx in
   (index param, ctor e) :: acc) args es.

Fixpoint elim_tuple (c : Inline.t) : result string t :=
  match c with
  | ISkip => ok c
  | IVardecl _ _ => ok c
  | IAssign type lhs rhs =>
    elim_tuple_assign type lhs rhs
  | IConditional typ g tru fls =>
    let* gs' := elim_tuple_expr g in
    let* g' := extract_single gs' "TypeError conditional must be a singleton" in
    let* tru' := elim_tuple tru in
    let+ fls' := elim_tuple fls in
    IConditional typ g' tru' fls'
  | ISeq c1 c2 =>
    let* c1' := elim_tuple c1 in
    let+ c2' := elim_tuple c2 in
    ISeq c1' c2'
  | IBlock blk =>
    let+ blk' := elim_tuple blk in
    IBlock blk'
  | IReturnVoid => ok c
  | IReturnFruit _ _ => ok c
  | IExit => ok c
  | IInvoke x keys actions =>
    (** TODO do we need to eliminate tuples in keys??*)
    let+ actions := List.fold_right (fun '(name, act) acc =>
                     let* act := elim_tuple act in
                     let+ acc := acc in
                     (name, act) :: acc) (ok []) actions in
    IInvoke x keys actions
  | IExternMethodCall extern method args ret  =>
      let arrow := elaborate_arguments args in
    ok (IExternMethodCall extern method arrow ret)
  end.

Definition header_fields  (e : E.e) (fields : list E.t) : list (E.e * E.t)  :=
  mapi (fun f typ => (E.Member typ f e, typ)) fields
    ++ [(E.Uop E.TBool E.IsValid e , E.TBool)].

Definition header_elaboration_assign  (lhs rhs : E.e) (fields : list E.t) : result string t :=
  let lhs_members := header_fields  lhs fields in
  let rhs_members := header_fields  rhs fields in
  let+ assigns := zip lhs_members rhs_members  in
  let f := fun '((lhs_mem, typ), (rhs_mem, _)) acc => ISeq (IAssign typ lhs_mem rhs_mem ) acc  in
  List.fold_right f (ISkip ) assigns.

Fixpoint elaborate_headers (c : Inline.t) : result string Inline.t :=
  match c with
  | ISkip => ok c
  | IVardecl _ _ => ok c
  | IAssign type lhs rhs =>
    match type with
    | E.TStruct true fields =>
      header_elaboration_assign lhs rhs fields
    | _ => ok c
    end
  | IConditional guard_type guard tru fls =>
  (** TODO: elaborate headers in guard? *)
  let* tru' := elaborate_headers tru in
  let+ fls' := elaborate_headers fls in
  IConditional guard_type guard tru' fls'
| ISeq s1 s2 =>
  let* s1' := elaborate_headers s1 in
  let+ s2' := elaborate_headers s2 in
  ISeq s1' s2'

| IBlock b =>
  let+ b' := elaborate_headers b in
  IBlock b'
| IReturnVoid => ok c
| IReturnFruit _ _ => ok c
| IExit => ok c
| IInvoke x keys actions =>
  let opt_actions := map_snd elaborate_headers actions in
  let+ actions' := rred (List.map res_snd opt_actions) in
  IInvoke x keys actions'
| IExternMethodCall extern method args ret =>
    let arrow := elaborate_arguments args in
  ok (IExternMethodCall extern method arrow ret)
end.

Fixpoint ifold {A : Type} (n : nat) (f : nat -> A -> A) (init : A) :=
  match n with
  | O => init
  | S n' => f n (ifold n' f init)
  end.

Definition elaborate_extract extern args ret  : result string Inline.t :=
  match args with
  | [(hdr, (PAOut arg))] =>
    (*match arg with
     TODO: what to do here now?
      | E.ExprMember (E.THeaderStack fields num) mem header_stack  =>
      if String.eqb mem "next"
      then ok (extract_next extern fields num hdr header_stack )
      else let arrow := elaborate_arrowE arrow in
           ok (IExternMethodCall extern "extract" arrow )
    | _ => *)
      let arrow := elaborate_arguments args in
      ok (IExternMethodCall extern "extract" arrow ret)
    (*end*)
  | _ =>
    let arrow := (*elaborate_arguments*) args in
    ok (IExternMethodCall extern "extract" arrow ret)
  end.

Fixpoint elaborate_arrays (c : Inline.t) : result string Inline.t :=
  match c with
  | ISkip => ok c
  | IVardecl type x =>
    match type with
    | E.TArray size t =>
        ok (ifold (BinNat.N.to_nat size)
              (fun n acc => ISeq (IVardecl t (index_array_str x n)) acc) ISkip)
    | _ => ok c
    end
  | IAssign type lhs rhs =>
    match type with
    | E.TArray size htype =>
      match lhs, rhs with
      | E.Var ltyp lvar il, E.Var rtyp rvar ir =>
        let iter := ifold (BinNat.N.to_nat size) in
        (* Should these be `HeaderStackAccess`es? *)
        let lvars := iter (fun n => cons (index_array_str lvar n)) [] in
        let rvars := iter (fun n => cons (index_array_str rvar n)) [] in
        let+ lrvars := zip lvars rvars in
        let mk := E.Var htype in
        fold_right (fun '(lv, rv) acc => ISeq (IAssign htype (mk lv il) (mk lv ir)) acc) ISkip lrvars
      | _, _ =>
        (* Don't know how to translate anything but variables *)
        error "Tried to elaborate a header stack assignment that wasn't variables"
      end
    | _ => ok c
    end
  | IConditional gtyp guard tru fls =>
    (* TODO Eliminate header stack literals from expressions *)
    let* tru' := elaborate_arrays tru in
    let+ fls' := elaborate_arrays fls in
    IConditional gtyp guard tru' fls'

  | ISeq c1 c2 =>
    let* c1' := elaborate_arrays c1 in
    let+ c2' := elaborate_arrays c2 in
    ISeq c1' c2'

  | IBlock c =>
    let+ c' := elaborate_arrays c in
    IBlock c'

  | IReturnVoid => ok c
  | IReturnFruit _ _ => ok c
  | IExit => ok c
  | IInvoke x keys actions =>
    (* TODO: Do something with keys? *)
    let rec_act_call := fun acc_opt '(nm, act) =>
        let* acc := acc_opt in
        let+ act' := elaborate_arrays act in
        (nm, act') :: acc
    in
    let+ actions' := fold_left rec_act_call actions (ok []) in
    IInvoke x keys (rev actions')
  | IExternMethodCall extern method arrow ret =>
      (*if String.eqb method "extract"
    then elaborate_extract extern arrow ret
    else*)
      (*if List.existsb e_has_typ_var (List.map (paramarg_elim ∘ snd) arrow) then
        error "in elaborte args have type var" else*)
      let arrow := elaborate_arguments arrow in
      ok (IExternMethodCall extern method arrow ret)
  end.

Definition struct_fields (s : string) (fields : list E.t) : list (string * E.t)  :=
  fold_righti (fun f typ acc => (s ++ "." ++ string_of_nat f, typ) :: acc ) [] fields.

(** TODO: Compiler pass to elaborate structs *)
Fixpoint elaborate_structs (c : Inline.t) : result string Inline.t :=
  match c with
  | ISkip => ok c
  | IVardecl type s =>
    match type with
    | E.TStruct false fields =>
        let vars := struct_fields s fields in
      let elabd_hdr_decls :=
        fold_left (fun acc '(var_str, var_typ) => ISeq (IVardecl var_typ var_str) acc) vars ISkip in
      ok elabd_hdr_decls
    | _ => ok c
    end
  | IAssign type lhs rhs =>
    match type with
    | E.TStruct false fields =>
      (** TODO : What other assignments to headers are legal? EHeader? EStruct? *)
      match lhs, rhs with
      | E.Var _ l il, E.Var _ r ir =>
        let lvars := struct_fields l fields in
        let rvars := struct_fields r fields in
        let+ lrvars := zip lvars rvars in
        fold_right
          (fun '((lvar, ltyp),(rvar, rtyp)) acc
           => ISeq (IAssign ltyp (E.Var ltyp lvar il) (E.Var rtyp rvar ir)) acc) ISkip lrvars
      | E.Var _ l il, E.Lists E.lists_struct explicit_fields =>
        let lvars := struct_fields l fields in
        let assign_fields := fun '(lvar, ltyp) acc_opt =>
             let* acc := acc_opt in
             let*~ rval := F.find_value (String.eqb lvar)
                             (List.combine
                                (List.map string_of_nat (seq 0 (List.length explicit_fields)))
                                explicit_fields) else "couldnt find field name in struct literal "in
             ok (ISeq (IAssign ltyp (E.Var ltyp lvar il) rval) acc) in
        fold_right assign_fields
           (ok ISkip)
           lvars
      | _, _ =>
         error "Can only elaborate struct assignments of the form var := {var | struct literal}"
      end
    | _ => ok c
  end
  | IConditional guard_type guard tru fls =>
    (** TODO: elaborate headers in guard? *)
    let* tru' := elaborate_structs tru in
    let+ fls' := elaborate_structs fls in
    IConditional guard_type guard tru' fls'
  | ISeq s1 s2 =>
    let* s1' := elaborate_structs s1 in
    let+ s2' := elaborate_structs s2 in
    ISeq s1' s2'

  | IBlock b =>
    let+ b' := elaborate_structs b in
    IBlock b'
  | IReturnVoid => ok c
  | IReturnFruit _ _ => ok c
  | IExit => ok c
  | IInvoke x keys actions =>
    let opt_actions := map_snd elaborate_structs actions in
    let+ actions' := rred (List.map res_snd opt_actions) in
    IInvoke x keys actions'
  | IExternMethodCall extern method arrow ret =>
      let arrow := elaborate_arguments arrow in
    ok (IExternMethodCall extern method arrow ret)
end.

Fixpoint eliminate_slice_assignments (c : t) : result string t :=
  match c with
  | ISkip => ok c
  | IVardecl _ _ => ok c
  | IAssign typ (E.Slice hi lo e) rhs =>
    let lhs_typ := t_of_e e in
    let concat := fun typ => E.Bop typ E.PlusPlus in
    let mk_new_rhs : positive -> E.e := fun w =>
      let upper := E.Slice w (BinPos.Pos.succ hi) e in
      let lower := E.Slice (BinPos.Pos.pred lo) (pos 0) e in
      let mid_type := E.TBit (Npos (BinPos.Pos.sub w lo)) in
      concat lhs_typ (concat mid_type upper rhs) lower in
    let* (rhs' : E.e) := match lhs_typ with
                 | E.TBit w => ok (mk_new_rhs (posN w))
                 | E.TInt w => ok (mk_new_rhs w)
                 | _ => error "Cannot get width"
                                end in
    ok (IAssign lhs_typ e rhs')
  | IAssign _ _ _ => ok c
  | IConditional typ guard tru fls =>
    let* tru' := eliminate_slice_assignments tru in
    let+ fls' := eliminate_slice_assignments fls in
    IConditional typ guard tru' fls'
  | ISeq s1 s2 =>
    let* s1' := eliminate_slice_assignments s1 in
    let+ s2' := eliminate_slice_assignments s2 in
    ISeq s1 s2
  | IBlock blk =>
    let+ blk' := eliminate_slice_assignments blk in
    IBlock blk'
  | IReturnVoid => ok c
  | IReturnFruit _ _ => ok c
  | IExit => ok c
  | IInvoke tbl keys actions =>
    let+ actions' := F.fold (fun name act acts =>
             let* act' := eliminate_slice_assignments act in
             let+ acts' := acts in
             (name, act') :: acts') actions (ok []) in
    IInvoke tbl keys actions'
  | IExternMethodCall _ _ _ _ => ok c
  end.

Definition inline_assert (check : E.e)  : t :=
  let args := [("check", PAIn check)] in
  IExternMethodCall "_" "assert" args None.

Definition isValid (hdr : E.e) : E.e :=
  E.Uop E.TBool E.IsValid hdr .

Fixpoint header_asserts (e : E.e) : result string t :=
  match e with
  | E.Bool _ | E.Bit _ _
  | E.Int _ _ | E.Var _ _ _
  | E.Error _  =>  ok ISkip
  | E.Member type name e => ok ISkip
  | E.Slice _ _ e  =>
    header_asserts e 
  | E.Cast _ e  =>
    header_asserts e 
  | E.Uop _ E.IsValid e  =>
    ok (ISkip )
  | E.Uop _ _ e  =>
    header_asserts e 
  | E.Bop _ _ lhs rhs  =>
    let* lhs_asserts := header_asserts lhs  in
    let+ rhs_asserts := header_asserts rhs  in
    ISeq lhs_asserts rhs_asserts 
  | E.Lists E.lists_struct _ =>
    error "[ERROR] [header_asserts] structs should be factored out by now"
  | E.Lists (E.lists_header _) _ =>
    error "[ERROR] [header_asserts] header literals should be factored out by now"
  | E.Lists (E.lists_array _) _ =>
    error "[ERROR] [header_asserts] array literals should be factored out by now"
  | E.Index _ _ _ =>
    error "[ERROR] [header_asserts] array indexing should be factored out by now"
  end.


Definition get_from_paramarg {A : Set} (pa : paramarg A A) :=
  match pa with
  | PAIn a => a
  | PAOut a => a
  | PAInOut a => a
  end.

Fixpoint assert_headers_valid_before_use (c : t) : result string t :=
  match c with
  | ISkip
  | IVardecl _ _ => ok c
  | IAssign _ lhs rhs  =>
    let* lhs_asserts := header_asserts lhs  in
    let+ rhs_asserts := header_asserts rhs  in
    ISeq (ISeq lhs_asserts rhs_asserts ) c 
  | IConditional typ guard tru fls  =>
    let* tru' := assert_headers_valid_before_use tru in
    let* fls' := assert_headers_valid_before_use fls in
    let+ guard_asserts := header_asserts guard  in
    ISeq guard_asserts (IConditional typ guard tru' fls' ) 
  | ISeq s1 s2  =>
    let* s1' := assert_headers_valid_before_use s1 in
    let+ s2' := assert_headers_valid_before_use s2 in
    ISeq s1' s2' 
  | IBlock blk =>
    let+ blk' := assert_headers_valid_before_use blk in
    IBlock blk'
  | IReturnVoid => ok c
  | IReturnFruit _ e =>
    let+ asserts := header_asserts e  in
    ISeq asserts c 
  | IExit => ok c
  | IInvoke t ks acts  =>
  (* Assume keys have been normalized, so dont to check them*)
    let+ acts' := rred (List.map (fun '(a,c) =>
                  let+ c' := assert_headers_valid_before_use c in
                  (a, c')) acts) in
    IInvoke t ks acts' 
  | IExternMethodCall ext method paramargs ret =>
    if String.eqb method "extract" then ok c else
    let+ asserts := List.fold_left (fun acc_asserts '(param, arg)  =>
                   let* acc_asserts := acc_asserts in
                   let arg_exp := get_from_paramarg arg in
                   let+ new_asserts := header_asserts arg_exp  in
                   ISeq acc_asserts new_asserts ) paramargs (ok (ISkip )) in
    ISeq asserts (IExternMethodCall ext method paramargs ret)
  end.

End Inline.
