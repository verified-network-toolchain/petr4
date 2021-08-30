Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.
Require Export Poulet4.P4cub.Util.Result.
Require Import Coq.Arith.EqNat.
Require Import String.
Open Scope string_scope.

Import Env.EnvNotations.

Import Result.
Import ResultNotations.

(** Compile to GCL *)
Module P := P4cub.
Module ST := P.Stmt.
Module CD := P.Control.ControlDecl.
Module E := P.Expr.
Module F := P.F.

Variable tags_t : Type.

Fixpoint list_eq {A : Type} (eq : A -> A -> bool) (s1 s2 : list A) : bool  :=
  match s1,s2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | x::xs, y::ys => andb (eq x y) (list_eq eq xs ys)
  end.

Fixpoint zip {A B : Type} (xs : list A) (ys : list B) : result (list (A * B)) :=
  match xs, ys with
  | [],[] => ok []
  | [], _ => error "First zipped list was shorter than the second"
  | _, [] => error "First zipped list was longer than the second"
  | x::xs, y::ys =>
    let** xys := zip xs ys in
    cons (x,y) xys
  end.

Fixpoint rred {A : Type} (os : list (result A)) : result (list A) :=
  match os with
  | [] => ok []
  | Error _ s :: _ => error s
  | (Ok _ x) :: os =>
    let** xs := rred os in
    x :: xs
  end.

Fixpoint fold_lefti { A B : Type } (f : nat -> A -> B -> B) (init : B) (lst : list A) : B :=
  snd (fold_left (fun '(n, b) a => (S n, f n a b)) lst (O, init)).

Definition opt_snd { A B : Type } (p : A * option B ) : option (A * B) :=
  match p with
  | (_, None) => None
  | (a, Some b) => Some (a,b)
  end.

Definition res_snd { A B : Type } (p : A * result B ) : result (A * B) :=
  match p with
  | (_, Error _ s) => error s
  | (a, Ok _ b) => ok (a, b)
  end.

Definition snd_res_map {A B C : Type} (f : B -> result C) (p : A * B) : result (A * C) :=
  let (x,y) := p in
  let** z := f y in
  (x, z).

Definition union_map_snd {A B C : Type} (f : B -> result C) (xs : list (A * B)) : result (list (A * C)) :=
  rred (List.map (snd_res_map f) xs).

Definition map_snd {A B C : Type} (f : B -> C) (ps : list (A * B)) : list (A * C) :=
  List.map (fun '(a, b) => (a, f b)) ps.

(* Ripped from Software foundations : https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match Nat.modulo n 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
  | 0 => acc'
  | S time' =>
    match Nat.div n 10 with
    | 0 => acc'
    | n' => string_of_nat_aux time' n' acc'
    end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Fixpoint string_member (x : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | y::ys =>
    if String.eqb x y
    then true
    else string_member x ys
  end.

Fixpoint intersect_string_list (xs ys : list string) : list string :=
  match xs with
  | [] => []
  | x::xs =>
    if string_member x ys
    then x::(intersect_string_list xs ys)
    else intersect_string_list xs ys
  end.

Module Ctx.
  Record t : Type :=
    mkCtx { stack : list nat; (* The current block stack *)
            used : list nat;  (* indices that have already been used *)
            locals : list string; (* variables in the current scope *)
            may_have_exited: bool;
            may_have_returned: bool;
          }.

  Definition initial :=
    {| stack := [0];
       used := [];
       locals := [];
       may_have_exited  := false;
       may_have_returned := false;
    |}.

  Definition incr (ctx : t) : t :=
    let new_idx := S(list_max (ctx.(stack) ++ ctx.(used))) in
    {| stack := new_idx :: ctx.(stack);
       used := ctx.(used);
       locals := [];
       may_have_exited := ctx.(may_have_exited);
       may_have_returned := false;
    |}.

  Definition current (ctx : t) : result nat :=
    match ctx.(stack) with
    | [] => error "Tried to get context counter from empty context"
    | idx :: _ => ok idx
    end.

  Definition decr (old_ctx : t) (ctx : t)  : result (t) :=
    match ctx.(stack) with
    | [] => error "Tried decrement empty counter"
    | idx :: idxs =>
      let ctx' := {| stack := idxs;
                     used := idx :: ctx.(stack);
                     locals := old_ctx.(locals);
                     may_have_exited := old_ctx.(may_have_exited) || ctx.(may_have_exited);
                     may_have_returned := old_ctx.(may_have_returned);
                  |} in
      ok ctx'
    end.

  Definition update_exit (ctx : t) (b : bool) :=
    {| stack := ctx.(stack);
       used := ctx.(used);
       locals := ctx.(locals);
       may_have_exited := b;
       may_have_returned := ctx.(may_have_returned)
    |}.

  Definition join (tctx fctx : t) : result t :=
    if list_eq Nat.eqb tctx.(stack) fctx.(stack)
    then ok {| stack := tctx.(stack);
                 used := tctx.(used) ++ fctx.(used);
                 locals := intersect_string_list tctx.(locals) fctx.(locals);
                 may_have_exited := tctx.(may_have_exited) || fctx.(may_have_exited);
                 may_have_returned := tctx.(may_have_returned) || fctx.(may_have_returned)
              |}
    else error "Tried to join two contexts with different context counters".

  Definition retvar_name (ctx : t) : string :=
    fold_right (fun idx acc => acc ++ (string_of_nat idx)) "return" ctx.(stack).

  Definition retvar (ctx : t) (i : tags_t) : E.e tags_t :=
    E.EVar E.TBool (retvar_name ctx) i.

  Definition add_to_scope (ctx : t) (v : string) :=
    {| stack := ctx.(stack);
       used := ctx.(used);
       locals := v :: ctx.(locals);
       may_have_exited := ctx.(may_have_exited);
       may_have_returned := ctx.(may_have_returned);
    |}.

  Definition is_local (ctx : t) (v : string) : bool :=
    string_member v (ctx.(locals)).

  Definition scope_name (v : string) (idx : nat) : string :=
    v ++ "_____" ++ string_of_nat idx.


  Definition relabel_for_scope (ctx : t) (v : string) : string :=
    if is_local ctx v
    then match current ctx with
         | Error _ _ => v
         | Ok _ idx => scope_name v idx
         end
    else v.

End Ctx.

Definition expenv : Type := Env.t string (E.e tags_t).

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
  | E.ESlice e τ hi lo i =>
    E.ESlice (subst_e η e) τ hi lo i
  | E.ECast type arg i =>
    E.ECast type (subst_e η arg) i
  | E.EUop op type arg i =>
    E.EUop op type (subst_e η arg) i
  | E.EBop op ltype rtype l r i =>
    E.EBop op ltype rtype (subst_e η l) (subst_e η r) i
  | E.ETuple es i =>
    E.ETuple (List.map (subst_e η) es) i
  | E.EStruct fields i =>
    E.EStruct (F.map (fun '(t,e) => (t, subst_e η e)) fields) i
  | E.EHeader fields valid i =>
    E.EHeader (F.map (fun '(t,e) => (t, subst_e η e)) fields) (subst_e η valid) i
  | E.EExprMember mem expr_type arg i =>
    E.EExprMember mem expr_type (subst_e η arg) i
  | E.EError _ _ => e
  | E.EMatchKind _ _ => e
  | E.EHeaderStack fields headers size ni i =>
    E.EHeaderStack fields (List.map (subst_e η) headers) size ni i
  | E.EHeaderStackAccess stack idx i =>
    E.EHeaderStackAccess (subst_e η stack) idx i
  end.


Module Inline.
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
  | IExternMethodCall (extn : string) (method : string) (args : ST.E.arrowE tags_t) (i : tags_t).

  Fixpoint subst_t (η : expenv) (c : t) : (t * expenv) :=
    match c with
    | ISkip i => (ISkip i, η)
    | IVardecl type x i  =>
      (IVardecl type x i, Env.remove x η)
    | IAssign t lhs rhs i =>
      (IAssign t (subst_e η lhs) (subst_e η lhs) i , η)
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
    | IReturnFruit _ _ _ => (c,η)
    | IExit _ => (c,η)
    | IInvoke x keys actions i =>
      let keys' := List.map (fun '(t,m,k) => (t, subst_e η m, k)) keys in
      let actions' := List.map (fun '(s,a) => (s, fst(subst_t η a))) actions in
      (IInvoke x keys' actions' i, η)

    | IExternMethodCall extn method (P.Arrow pas returns) i =>
      let f := fun '(t,e) => (t,subst_e η e) in
      let pas' := F.map (P.paramarg_map f f) pas in
      (IExternMethodCall extn method (P.Arrow pas' returns) i, η)
    end.

  Definition copy (args : ST.E.args tags_t) : expenv :=
    F.fold (fun param arg η => match arg with
                               | P.PAIn (_,e) => Env.bind param e η
                               | P.PAInOut (_,e) => Env.bind param e η
                               | P.PAOut (_,e) => Env.bind param e η
                               end)
           args (Env.empty EquivUtil.string (E.e tags_t)).

  Fixpoint inline (n : nat)
           (cienv : @cienv tags_t)
           (aenv : @aenv tags_t)
           (tenv : @tenv tags_t)
           (fenv : fenv)
           (s : ST.s tags_t)
           {struct n} : result t :=
    match n with
    | 0 => error "Inliner ran out of gas"
    | S n0 =>
      match s with
      | ST.SSkip i =>
        ok (ISkip i)

      | ST.SVardecl typ x i =>
        ok (IVardecl typ x i)

      | ST.SAssign type lhs rhs i =>
        ok (IAssign type lhs rhs i)

      | ST.SConditional gtyp guard tru_blk fls_blk i =>
        let* tru_blk' := inline n0 cienv aenv tenv fenv tru_blk in
        let** fls_blk' := inline n0 cienv aenv tenv fenv fls_blk in
        IConditional gtyp guard tru_blk' fls_blk' i

      | ST.SSeq s1 s2 i =>
        let* i1 := inline n0 cienv aenv tenv fenv s1 in
        let** i2 := inline n0 cienv aenv tenv fenv s2 in
        ISeq i1 i2 i

      | ST.SBlock s =>
        let** blk := inline n0 cienv aenv tenv fenv s in
        IBlock blk

      | ST.SFunCall f (P.Arrow args ret) i =>
        let*~ fdecl := Env.find f fenv else "could not find function in environment" in
        match fdecl with
        | FDecl ε fenv' body =>
          (** TODO check copy-in/copy-out *)
          let** rslt := inline n0 cienv aenv tenv fenv' body in
          let η := copy args in
          IBlock rslt
        end
      | ST.SActCall a args i =>
        let*~ adecl := Env.find a aenv else ("could not find action " ++ a ++ " in environment") in
        match adecl with
        | ADecl ε fenv' aenv' externs body =>
          (** TODO handle copy-in/copy-out *)
          let** rslt := inline n0 cienv aenv' tenv fenv' body in
          let η := copy args in
          IBlock (fst (subst_t η rslt))
        end
      | ST.SApply ci args i =>
        let*~ cinst := Env.find ci cienv else "could not find controller instance in environment" in
        match cinst with
        | CInst closure fenv' cienv' tenv' aenv' externs' apply_blk =>
          let** rslt := inline n0 cienv' aenv' tenv' fenv' apply_blk in
          (** TODO check copy-in/copy-out *)
          let η := copy args in
          IBlock (fst (subst_t η rslt))
        end

      | ST.SReturnVoid i =>
        ok (IReturnVoid i)

      | ST.SReturnFruit typ expr i =>
        ok (IReturnFruit typ expr i)

      | ST.SExit i =>
        ok (IExit i)

      | ST.SInvoke t i =>
        let*~ tdecl := Env.find t tenv else "could not find table in environment" in
        match tdecl with
        | CD.Table keys actions =>
          let act_to_gcl := fun a =>
            let*~ adecl := Env.find a aenv else "could not find action " ++ a ++ " in environment" in
            match adecl with
            | ADecl _ fenv' aenv' externs body =>
              (** TODO handle copy-in/copy-out *)
              inline n0 cienv aenv tenv fenv body
            end
          in
          let* acts := rred (List.map act_to_gcl actions) in
          let** named_acts := zip actions acts in
          IInvoke t keys named_acts i
        end

      | ST.SExternMethodCall ext method args i =>
        ok (IExternMethodCall ext method args i)
      end
    end.

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
      let** te := zip types es in
      fold_lefti (seq_tuple_elem_assign x i) (Inline.ISkip i) te
    | _,_ => ok (Inline.IAssign ltyp lhs rhs i)
    end.

  Definition res_snd { A B : Type } (p : A * result B ) : result (A * B) :=
    match p with
    | (_, Error _ s) => error s
    | (a, Ok _ b) => ok (a, b)
    end.

  Fixpoint elim_tuple (c : Inline.t) : result t :=
    match c with
    | ISkip _ => ok c
    | IVardecl _ _ _ => ok c
    | IAssign type lhs rhs i =>
      elim_tuple_assign type lhs rhs i
    | IConditional typ g tru fls i =>
      let* tru' := elim_tuple tru in
      let** fls' := elim_tuple fls in
      IConditional typ g tru' fls' i
    | ISeq c1 c2 i =>
      let* c1' := elim_tuple c1 in
      let** c2' := elim_tuple c2 in
      ISeq c1' c2' i
    | IBlock blk =>
      let** blk' := elim_tuple blk in
      IBlock blk'
    | IReturnVoid _ => ok c
    | IReturnFruit _ _ _ => ok c
    | IExit _ => ok c
    | IInvoke x keys actions i =>
      (** TODO do we need to eliminate tuples in keys??*)
      let opt_actions := map_snd elim_tuple actions in
      let** actions' := rred (List.map res_snd opt_actions) in
      IInvoke x keys actions' i
    | IExternMethodCall _ _ _ _ =>
      (** TODO do we need to eliminate tuples in extern arguments? *)
      ok c
    end.

  (** TODO: Compiler pass to convert int<> -> bit<> *)
  Fixpoint encode_ints_as_bvs (c : Inline.t) : option Inline.t :=
    None.

  Fixpoint header_fields (s : string) (fields : F.fs string E.t) : list (string * E.t)  :=
    F.fold (fun f typ acc => (s ++ "__f__" ++ f, typ) :: acc ) fields [(s ++ ".is_valid", E.TBool)].

  Fixpoint elaborate_headers (c : Inline.t) : result Inline.t :=
    match c with
    | ISkip _ => ok c
    | IVardecl type s i =>
      (** TODO elaborate header if type = THeader *)
      match type with
      | E.THeader fields =>
        let vars := header_fields s fields in
        let elabd_hdr_decls := fold_left (fun acc '(var_str, var_typ) => ISeq (IVardecl var_typ var_str i) acc i) vars (ISkip i) in
        ok elabd_hdr_decls
      | _ => ok c
      end
    | IAssign type lhs rhs i =>
      match type with
      | E.THeader fields =>
        (** TODO : What other assignments to headers are legal? EHeader? EStruct? *)
        match lhs, rhs with
        | E.EVar _ l il, E.EVar _ r ir =>
          let lvars := header_fields l fields in
          let rvars := header_fields r fields in
          let** lrvars := zip lvars rvars in
          fold_right (fun '((lvar, ltyp),(rvar, rtyp)) acc => ISeq (IAssign ltyp (E.EVar ltyp lvar il) (E.EVar rtyp rvar ir) i) acc i) (ISkip i) lrvars
        | E.EVar _ l il, E.EHeader explicit_fields valid i =>
          let lvars := header_fields l fields in
          let assign_fields := fun '(lvar, ltyp) acc_res =>
               let* acc := acc_res in
               let*~ (_, rval) := F.find_value (eqb lvar) explicit_fields else "couldn't find field in field list" in
               ok (ISeq (IAssign ltyp (E.EVar ltyp lvar il) rval i) acc i)
          in
          fold_right assign_fields
                     (ok (IAssign E.TBool (E.EVar E.TBool (l ++ ".is_valid") il) valid i))
                     lvars

        | _, _ =>
          error "Can only copy variables or header literals type header"
        end
      | _ => ok c
      end

    | IConditional guard_type guard tru fls i =>
      (** TODO: elaborate headers in guard? *)
      let* tru' := elaborate_headers tru in
      let** fls' := elaborate_headers fls in
      IConditional guard_type guard tru' fls' i
    | ISeq s1 s2 i =>
      let* s1' := elaborate_headers s1 in
      let** s2' := elaborate_headers s2 in
      ISeq s1' s2' i

    | IBlock b =>
      let** b' := elaborate_headers b in
      IBlock b'
    | IReturnVoid _ => ok c
    | IReturnFruit _ _ _ => ok c
    | IExit _ => ok c
    | IInvoke x keys actions i =>
      let opt_actions := map_snd elaborate_headers actions in
      let** actions' := rred (List.map res_snd opt_actions) in
      IInvoke x keys actions' i
    | IExternMethodCall _ _ _ _ =>
      (* TODO Do we need to eliminate tuples in arguments? *)
      ok c
    end.


  Fixpoint ifold {A : Type} (n : nat) (f : nat -> A -> A) (init : A) :=
    match n with
    | O => init
    | S n' => f n (ifold n' f init)
    end.


  Fixpoint elaborate_header_stacks (c : Inline.t) : result Inline.t :=
    match c with
    | ISkip _ => ok c
    | IVardecl type x i =>
      match type with
      | E.THeaderStack fields size =>
        ok (ifold (BinPos.Pos.to_nat size)
                    (fun n acc => ISeq (IVardecl (E.THeader fields) (x ++ "[" ++ string_of_nat n ++ "]") i) acc i) (ISkip i))
      | _ => ok c
      end
    | IAssign type lhs rhs i =>
      match type with
      | E.THeaderStack fields size =>
        match lhs, rhs with
        | E.EVar ltyp lvar il, E.EVar rtyp rvar ir =>
          let iter := ifold (BinPos.Pos.to_nat size) in
          (* Should these be `HeaderStackAccess`es? *)
          let lvars := iter (fun n => cons (lvar ++ "[" ++ string_of_nat n ++ "]")) [] in
          let rvars := iter (fun n => cons (rvar ++ "[" ++ string_of_nat n ++ "]")) [] in
          let** lrvars := zip lvars rvars in
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
      let** fls' := elaborate_header_stacks fls in
      IConditional gtyp guard tru' fls' i

    | ISeq c1 c2 i =>
      let* c1' := elaborate_header_stacks c1 in
      let** c2' := elaborate_header_stacks c2 in
      ISeq c1' c2' i

    | IBlock c =>
      let** c' := elaborate_header_stacks c in
      IBlock c'

    | IReturnVoid _ => ok c
    | IReturnFruit _ _ _ => ok c
    | IExit _ => ok c
    | IInvoke x keys actions i =>
      (* TODO: Do something with keys? *)
      let rec_act_call := fun '(nm, act) acc_opt =>
          let* acc := acc_opt in
          let** act' := elaborate_header_stacks act in
          (nm, act') :: acc
      in
      let** actions' := fold_right rec_act_call (ok []) actions in
      IInvoke x keys actions' i
    | IExternMethodCall _ _ _ _ =>
      (* TODO: Do something with arguments? *)
      ok c
    end.

  Fixpoint struct_fields (s : string) (fields : F.fs string E.t) : list (string * E.t)  :=
    F.fold (fun f typ acc => (s ++ "__s__" ++ f, typ) :: acc ) fields [].

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
          let** lrvars := zip lvars rvars in
          fold_right (fun '((lvar, ltyp),(rvar, rtyp)) acc => ISeq (IAssign ltyp (E.EVar ltyp lvar il) (E.EVar rtyp rvar ir) i) acc i) (ISkip i) lrvars
        | E.EVar _ l il, E.EStruct explicit_fields i =>
          let lvars := struct_fields l fields in
          let assign_fields := fun '(lvar, ltyp) acc_opt =>
               let* acc := acc_opt in
               let*~ (_, rval) := F.find_value (eqb lvar) explicit_fields else "couldnt find field name in struct literal "in
               ok (ISeq (IAssign ltyp (E.EVar ltyp lvar il) rval i) acc i)
          in
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
      let* tru' := elaborate_headers tru in
      let** fls' := elaborate_headers fls in
      IConditional guard_type guard tru' fls' i
    | ISeq s1 s2 i =>
      let* s1' := elaborate_headers s1 in
      let** s2' := elaborate_headers s2 in
      ISeq s1' s2' i

    | IBlock b =>
      let** b' := elaborate_headers b in
      IBlock b'
    | IReturnVoid _ => ok c
    | IReturnFruit _ _ _ => ok c
    | IExit _ => ok c
    | IInvoke x keys actions i =>
      let opt_actions := map_snd elaborate_structs actions in
      let** actions' := rred (List.map res_snd opt_actions) in
      IInvoke x keys actions' i
    | IExternMethodCall _ _ _ _ =>
      (* TODO Do we need to eliminate tuples in arguments? *)
      ok c
    end.
End Inline.

Module GCL.
  Inductive t {lvalue rvalue form : Type} : Type :=
  | GSkip (i : tags_t)
  | GAssign (type : E.t) (lhs : lvalue) (rhs : rvalue) (i : tags_t)
  | GSeq (g1 g2 : t)
  | GChoice (g1 g2 : t)
  | GAssume (phi : form)
  | GAssert (phi : form).

  Definition g_sequence {L R F : Type} (i : tags_t) : list (@t L R F) -> @t L R F :=
    fold_right GSeq (GSkip i).

  Module BitVec.
    Inductive bop :=
    | BVPlus
    | BVMinus
    | BVTimes
    | BVConcat
    | BVShl
    | BVShr
    | BVAnd
    | BVOr
    | BVXor.

    Inductive uop :=
    | BVNeg
    | BVCast (i : positive)
    | BVSlice (hi lo : positive).

    Inductive t :=
    | BitVec (n : positive) (w : positive) (i : tags_t)
    | BVVar (x : string) (w : positive) (i : tags_t)
    | BinOp (op : bop) (u v : t) (i : tags_t)
    | UnOp (op : uop) (v : t) (i : tags_t).

    Definition add := BinOp BVPlus.
    Definition sub := BinOp BVMinus.
    Definition mul := BinOp BVTimes.
    Definition app := BinOp BVConcat.
    Definition shl := BinOp BVShl.
    Definition shr := BinOp BVShr.
    Definition band := BinOp BVAnd.
    Definition bor := BinOp BVOr.
    Definition bxor := BinOp BVXor.

  End BitVec.

  Inductive lbop := | LOr | LAnd | LImp | LIff.
  Inductive lcomp := | LEq | LLe | LLt | LGe | LGt | LNeq.
  Inductive form :=
  | LBool (b : bool) (i : tags_t)
  | LBop (op : lbop) (ϕ ψ : form) (i : tags_t)
  | LNot (ϕ : form) (i : tags_t)
  | LVar (x : string) (i : tags_t)
  | LComp (comp : lcomp) (bv1 bv2 : BitVec.t) (i : tags_t)
  .

  Definition leq := LComp LEq.
  Definition lle := LComp LLe.
  Definition llt := LComp LLt.
  Definition lge := LComp LGe.
  Definition lgt := LComp LGt.
  Definition lne := LComp LNeq.

  Definition lor := LBop LOr.
  Definition land := LBop LAnd.
  Definition limp := LBop LImp.
  Definition liff := LBop LIff.

  Definition pos : (nat -> positive) := BinPos.Pos.of_nat.

  Definition is_true (x : string) (i : tags_t) : form :=
    LComp (LEq) (BitVec.BVVar x (pos 1) i) (BitVec.BitVec (pos 1) (pos 1) i) i.

  Definition exit (i : tags_t) : form := is_true "exit" i.
  Definition etrue (i : tags_t) : E.e tags_t := E.EBool true i.
  Definition efalse (i : tags_t) : E.e tags_t := E.EBool false i.
  Definition ite {lvalue rvalue : Type} (guard_type : E.t) (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not guard_type guard i)) fls).
  Definition iteb {lvalue rvalue : Type} (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not E.TBool guard i)) fls).


  Module Arch.
    Definition extern : Type := Env.t string (@t string BitVec.t form).
    Definition model : Type := Env.t string extern.
    Definition find (m : model) (e f : string) : result t :=
      let*~ ext := Env.find e m else "couldn't find extern " ++ e ++ " in model" in
      let*~ fn := Env.find f ext else "couldn't find field " ++ f ++ " in extern" in
      ok fn.
    Definition empty : model := Env.empty string extern.
  End Arch.

  Module I := Inline.
  Module Translate.
  Section Instr.
    Definition target := @t string BitVec.t form.
    Variable instr : (string -> tags_t -> list (E.t * E.e tags_t * E.matchkind) -> list (string * target) -> result target).

    Fixpoint scopify (ctx : Ctx.t) (e : E.e tags_t) : E.e tags_t :=
      match e with
      | E.EBool _ _ => e
      | E.EBit _ _ _ => e
      | E.EInt _ _ _ => e
      | E.EVar typ x i =>
        let x' := Ctx.relabel_for_scope ctx x in
        E.EVar typ x' i
      | E.ESlice n τ hi lo i =>
        E.ESlice (scopify ctx n) τ hi lo i
      | E.ECast type arg i =>
        E.ECast type (scopify ctx arg) i
      | E.EUop op type arg i =>
        E.EUop op type (scopify ctx arg) i
      | E.EBop op lhs_type rhs_type lhs rhs i =>
        E.EBop op lhs_type rhs_type (scopify ctx lhs) (scopify ctx rhs) i

      | E.ETuple es i =>
        E.ETuple (List.map (scopify ctx) es) i
      | E.EStruct fields i =>
        E.EStruct (F.map (fun '(typ, exp) => (typ, scopify ctx exp)) fields) i
      | E.EHeader fields valid i =>
        E.EHeader (F.map (fun '(typ,exp) => (typ, scopify ctx exp)) fields) (scopify ctx valid) i
      | E.EExprMember mem expr_type arg i =>
        E.EExprMember mem expr_type (scopify ctx arg) i
      | E.EError _ _ => e
      | E.EMatchKind _ _ => e
      | E.EHeaderStack fields headers size next_index i =>
        E.EHeaderStack fields (List.map (scopify ctx) headers) size next_index i
      | E.EHeaderStackAccess stack index i =>
        E.EHeaderStackAccess (scopify ctx stack) index i
      end.
    (**[]*)

    Definition iteb (guard : form) (tru fls : target) (i : tags_t) : target :=
      GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (LNot guard i)) fls).

    Definition seq (i : tags_t) (res1 res2 : (target * Ctx.t)) : target * Ctx.t :=
      let (g1, ctx1) := res1 in
      let (g2, ctx2) := res2 in
      let g2' :=
          if Ctx.may_have_returned ctx1
          then (iteb (is_true (Ctx.retvar_name ctx1) i) (GSkip i) g2 i)
          else g2 in
      let g2'' :=
          if Ctx.may_have_exited ctx1
          then (iteb (exit i) (GSkip i) g2 i)
          else g2' in
      (GSeq g1 g2'', ctx2).

    Definition string_of_z (x : Z) :=
      if BinInt.Z.ltb x (Z0)
      then "-" ++ string_of_nat (BinInt.Z.abs_nat x)
      else string_of_nat (BinInt.Z.abs_nat x).

    Fixpoint to_lvalue (e : E.e tags_t) : result string :=
      match e with
      | E.EBool _ _ => error "Boolean Literals are not lvalues"
      | E.EBit _ _ _ => error "BitVector Literals are not lvalues"
      | E.EInt _ _ _ => error "Integer literals are not lvalues"
      | E.EVar t x i => ok x
      | E.ESlice e τ hi lo pos =>
        (* TODO :: Allow assignment to slices *)
        error "[FIXME] Slices are not l-values "
      | E.ECast _ _ _ => error "Casts are not l-values"
      | E.EUop _ _ _ _ => error "Unary Operations are not l-values"
      | E.EBop _ _ _ _ _ _ => error "Binary Operations are not l-values"
      | E.ETuple _ _ => error "Explicit Tuples are not l-values"
      | E.EStruct _ _ => error "Explicit Structs are not l-values"
      | E.EHeader _ _ _ => error "Explicit Headers are not l-values"
      | E.EExprMember mem expr_type arg i =>
        let** lv := to_lvalue arg in
        lv ++ "." ++ mem
      | E.EError _ _ => error "errors are not l-values"
      | E.EMatchKind _ _ => error "Match Kinds are not l-values"
      | E.EHeaderStack _ _ _ _ _ => error "Header Stacks are not l-values"
      | E.EHeaderStackAccess stack index i =>
        let** lv := to_lvalue stack in
        (** TODO How to handle negative indices? **)
        lv ++ "["++ (string_of_z index) ++ "]"
      end.

    Definition width_of_type (t : E.t) : result positive :=
      match t with
      | E.TBool => ok (pos 1)
      | E.TBit w => ok w
      | E.TInt w => ok w
      | E.TError => error "Cannot get the width of an error Type"
      | E.TMatchKind => error "Cannot get the width of a Match Kind Type"
      | E.TTuple types => error "Cannot get the width of a Tuple Type"
      | E.TStruct fields => error "Cannot get the width of a Struct Type"
      | E.THeader fields => error "Cannot get the width of a Header Type"
      | E.THeaderStack fields size => error "Cannot get the width of a header stack type"
      end.

    Definition get_header_of_stack (stack : E.e tags_t) : result E.t :=
      match stack with
      | E.EHeaderStack fields headers size next_index i =>
        ok (E.THeader fields)
      | _ => error "Tried to get the base header of something other than a header stack."
      end.

    Fixpoint to_header_string (e : (E.e tags_t)) : result string :=
      match e with
      | E.EBool _ _ => error "A Boolean is not a header"
      | E.EBit _ _ _ => error "A bitvector literal is not a header"
      | E.EInt _ _ _ => error "An integer literal is not a header"
      | E.EVar t x i =>
        match t with
        | E.THeader _ => ok x
        | _ => error "Got variable, but the header itself was no good"
        end
      | E.ESlice _ _ _ _ _ => error "A Slice is not a header"
      | E.ECast _ _ _ => error "A Cast is not a header"
      | E.EUop _ _ _ _ => error "No unary operation is a header"
      | E.EBop _ _ _ _ _ _ => error "No binary operation is a header"
      | E.ETuple _ _ => error "A Tuple is not a header"
      | E.EStruct _ _ =>
        error "Structs are not headers"
      | E.EHeader _ _ _ =>
        error "Header literals should not be keys"
      | E.EExprMember mem expr_type arg i =>
        let** str := to_header_string arg in
        str ++ "." ++ mem
      | E.EError _ _ => error "errors are not header strings"
      | E.EMatchKind _ _ => error "MatchKinds are not header strings"
      | E.EHeaderStack _ _ _ _ _ =>
        error "[FIXME] Header stacks are not supported as table keys"
      | E.EHeaderStackAccess stack index i =>
        error "Header stack accesses as table keys should have been factored out in an earlier stage."
      end.

    Fixpoint to_rvalue (e : (E.e tags_t)) : result BitVec.t :=
      match e with
      | E.EBool b i =>
        if b
        then ok (BitVec.BitVec (pos 1) (pos 1) i)
        else ok (BitVec.BitVec (pos 0) (pos 1) i)
      | E.EBit w v i =>
        ok (BitVec.BitVec (BinInt.Z.to_pos v) w i)
      | E.EInt _ _ _ =>
        (** TODO Figure out how to handle ints *)
        error "[FIXME] Cannot translate signed ints to rvalues"
      | E.EVar t x i =>
        let** w := width_of_type t in
        BitVec.BVVar x w i

      | E.ESlice e τ hi lo i =>
        let** rv_e := to_rvalue e in
        BitVec.UnOp (BitVec.BVSlice hi lo) rv_e i

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => ok (BitVec.UnOp (BitVec.BVCast w) rvalue_arg i) in
        match type with
        | E.TBool => cast (pos 1)
        | E.TBit w => cast w
        | E.TInt w => error "[FIXME] Signed Integers are unimplemented "
        | _ =>
          error "Illegal cast, should've been caught by the type-checker"
        end
      | E.EUop op type arg i =>
        match op with
        | E.Not =>
          let** rv_arg := to_rvalue arg in
          BitVec.UnOp BitVec.BVNeg rv_arg i
        | E.BitNot =>
          let** rv_arg := to_rvalue arg in
          BitVec.UnOp BitVec.BVNeg rv_arg i
        | E.UMinus => error "[FIXME] Subtraction is unimplemented"
        | E.IsValid =>
          let** header := to_header_string arg in
          let hvld := header ++ ".is_valid" in
          BitVec.BVVar hvld (pos 1) i
        | E.SetValid => (* TODO @Rudy isn't this a command? *)
          error "SetValid as an expression is deprecated"
        | E.SetInValid =>
          error "SetInValid as an expression is deprecated"
        | E.NextIndex =>
          error "[FIXME] NextIndex for Header Stacks is unimplemented"
        | E.Size =>
          error "[FIXME] Size for Header Stacks is unimplmented"
        | E.Push n =>
          error "Push as an expression is deprecated"
        | E.Pop n =>
          error "Pop as an expression is deprecated"
        end
      | E.EBop op ltyp rtyp lhs rhs i =>
        let* l := to_rvalue lhs in
        let* r := to_rvalue rhs in
        let bin := fun o => ok (BitVec.BinOp o l r i) in
        match op with
        | E.Plus => bin BitVec.BVPlus
        | E.PlusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Minus => bin BitVec.BVMinus
        | E.MinusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Times => bin BitVec.BVTimes
        | E.Shl => bin BitVec.BVShl
        | E.Shr => bin BitVec.BVShr
        | E.Le => error "Typeerror: (<=) is a boolean, expected BV expression"
        | E.Ge => error "Typeerror: (>=) is a boolean, expected BV expression"
        | E.Lt => error "Typeerror: (<) is a boolean, expected BV expression"
        | E.Gt => error "Typeerror: (>) is a boolean, expected BV expression"
        | E.Eq => error "Typeerror: (=) is a boolean, expected BV expression"
        | E.NotEq => error "Typeerror: (!=) is a boolean, expected BV expression"
        | E.BitAnd => bin BitVec.BVAnd
        | E.BitXor => bin BitVec.BVXor
        | E.BitOr => bin BitVec.BVOr
        | E.PlusPlus => bin BitVec.BVConcat
        | E.And => error "Typeerror: (&&) is a boolean, expected BV expression"
        | E.Or => error "Typeerror: (||) is a boolean, expected BV expression"
        end
      | E.ETuple _ _ =>
        error "Tuples in the rvalue position should have been factored out by previous passes"
      | E.EStruct _ _ =>
        error "Structs in the rvalue position should have been factored out by previous passes"
      | E.EHeader _ _ _ =>
        error "Header in the rvalue positon should have been factored out by previous passes"
      | E.EExprMember mem expr_type arg i =>
        let* lv := to_lvalue arg in
        let** w := width_of_type expr_type in
        BitVec.BVVar (lv ++ "." ++ mem) w i
      | E.EError _ _ => error "errors are not rvalues."
      | E.EMatchKind _ _ => error "MatchKinds are not rvalues"
      | E.EHeaderStack _ _ _ _ _ =>
        error "Header stacks in the rvalue position should have been factored out by previous passes"
      | E.EHeaderStackAccess stack index i =>
        error "Header stack accesses in the rvalue position should have been factored out by previous passes."
      end.

    Definition isone (v : BitVec.t) (i :tags_t) : form :=
      LComp LEq v (BitVec.BitVec (pos 1) (pos 1) i) i.

    Print form.
    Fixpoint to_form (e : (E.e tags_t)) : result form :=
      match e with
      | E.EBool b i => ok (LBool b i)
      | E.EBit _ _ _ =>
        error "Typeerror: Bitvector literals are not booleans (perhaps you want to insert a cast?)"
      | E.EInt _ _ _ =>
        error "Typeerror: Signed Ints are not booleans (perhaps you want to insert a cast?)"
      | E.EVar t x i =>
        match t with
        | E.TBool => ok (LVar x i)
        | _ =>
          error "Typeerror: Expected a Boolean form, got something else (perhaps you want to insert a cast?)"
        end

      | E.ESlice e τ hi lo i =>
        error "Typeerror: BitVector Slices are not booleans (perhaps you want to insert a cast?)"

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => ok (isone (BitVec.UnOp (BitVec.BVCast w) rvalue_arg i) i) in
        match type with
        | E.TBool => cast (pos 1)
        | E.TBit w => cast w
        | E.TInt w => error "[FIXME] Handle Signed Integers"
        | _ =>
          error "Invalid Cast"
        end
      | E.EUop op type arg i =>
        let* rv_arg := to_rvalue arg in
        match op with
        | E.Not => ok (isone (BitVec.UnOp BitVec.BVNeg rv_arg i) i)
        | E.BitNot => error "Bitvector operations (!) are not booleans (perhaps you want to insert a cast?)"
        | E.UMinus => error "Saturating arithmetic (-) is not boolean (perhaps you want to insert a cast?)"
        | E.IsValid =>
          let** header := to_lvalue arg in
          let hvld := header ++ ".is_valid" in
          isone (BitVec.BVVar hvld (pos 1) i) i
        | E.SetValid =>
          error "SetValid is deprecated as an expression"
        | E.SetInValid =>
          error "SetInValid is deprecated as an expression"
        | E.NextIndex =>
          error "[FIXME] Next Index for stacks is unimplemented"
        | E.Size =>
          error "[FIXME] Size for stacks is unimplemented"
        | E.Push n =>
          error "Push is deprecated as an expression"
        | E.Pop n =>
          error "Pop is deprecated as an expression"
        end
      | E.EBop op ltyp rtyp lhs rhs i =>
        let bbin := fun _ => error "BitVector operators are not booleans (perhaps you want to insert a cast?)" in
        let lbin := fun o => let* l := to_form lhs in
                             let** r := to_form rhs in
                             LBop o l r i in
        let cbin := fun c => let* l := to_rvalue lhs in
                             let** r := to_rvalue rhs in
                             LComp c l r i in
        match op with
        | E.Plus => bbin BitVec.BVPlus
        | E.PlusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Minus => bbin BitVec.BVMinus
        | E.MinusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Times => bbin BitVec.BVTimes
        | E.Shl => bbin BitVec.BVShl
        | E.Shr => bbin BitVec.BVShr
        | E.Le => cbin LLe
        | E.Ge => cbin LGe
        | E.Lt => cbin LLt
        | E.Gt => cbin LGt
        | E.Eq => cbin LEq
        | E.NotEq => cbin LNeq
        | E.BitAnd => bbin BitVec.BVAnd
        | E.BitXor => bbin BitVec.BVXor
        | E.BitOr => bbin BitVec.BVOr
        | E.PlusPlus => error "BitVector operators are not booleans (perhaps you want to insert a cast?)"
        | E.And => lbin LAnd
        | E.Or => lbin LOr
        end
      | E.ETuple _ _ =>
        error "Tuples are not formulae"
      | E.EStruct _ _ =>
        error "Structs are not formulae"
      | E.EHeader _ _ _ =>
        error "Headers are not formulae"
      | E.EExprMember mem expr_type arg i =>
        let* lv := to_lvalue arg in
        let~ w := (width_of_type expr_type) over ("failed getting type of " ++ mem) in
        ok (isone (BitVec.BVVar lv w i) i)
      | E.EError _ _ =>
        error "errors are not formulae"
      | E.EMatchKind _ _ =>
        error "Matchkinds are not formulae"
      | E.EHeaderStack _ _ _ _ _ =>
        error "HeaderStacks are not formulae"
      | E.EHeaderStackAccess stack index i =>
        error "Headers (from header stack accesses) are not formulae"
      end.

    Definition cond (guard_type : E.t) (guard : E.e tags_t) (i : tags_t) (tres fres : (target * Ctx.t)) : result (target * Ctx.t) :=
      let (tg, tctx) := tres in
      let (fg, fctx) := fres in
      let* ctx := Ctx.join tctx fctx in
      let* phi := to_form guard in
      ok (iteb phi tg fg i, ctx).

    Fixpoint inline_to_gcl (ctx : Ctx.t) (arch : Arch.model) (s : I.t) : result (target * Ctx.t) :=
      match s with
      | I.ISkip i =>
        ok (GSkip i, ctx)

      | I.IVardecl typ x i =>
        ok (GSkip i, Ctx.add_to_scope ctx x)

      | I.IAssign type lhs rhs i =>
        let* lhs' := to_lvalue (scopify ctx lhs) in
        let** rhs' := to_rvalue (scopify ctx rhs) in
        let e := GAssign type lhs' rhs' i in
        (e, ctx)

      | I.IConditional guard_type guard tru_blk fls_blk i =>
        let* tru_blk' := inline_to_gcl ctx arch tru_blk in
        let* fls_blk' := inline_to_gcl ctx arch fls_blk in
        cond guard_type (scopify ctx guard) i tru_blk' fls_blk'

      | I.ISeq s1 s2 i =>
        let* g1 := inline_to_gcl ctx arch s1 in
        let** g2 := inline_to_gcl ctx arch s2 in
        seq i g1 g2

      | I.IBlock s =>
        let* (gcl, ctx') := inline_to_gcl (Ctx.incr ctx) arch s in
        let** ctx'' := Ctx.decr ctx ctx' in
        (gcl, ctx'')

      | I.IReturnVoid i =>
        let gasn := @GAssign string BitVec.t form in
        ok (gasn (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BitVec.BitVec (pos 1) (pos 1) i) i, ctx)

      | I.IReturnFruit typ expr i =>
        (** TODO create var for return type & save it *)
        ok (GAssign (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BitVec.BitVec (pos 1) (pos 1) i) i, ctx)

      | I.IExit i =>
        ok (GAssign (E.TBit (pos 1)) "exit" (BitVec.BitVec (pos 1) (pos 1) i) i, Ctx.update_exit ctx true)

      | I.IInvoke tbl keys actions i =>
        let* actions' := union_map_snd (fst >>=> inline_to_gcl ctx arch) actions in
        let** g := instr tbl i keys actions' in
        (g, ctx)

      | I.IExternMethodCall ext method args i =>
        (** TODO handle copy-in/copy-out) *)
        let** g := Arch.find arch ext method in
        (g, ctx)
      end.

    Definition p4cub_statement_to_gcl (gas : nat)
               (cienv : @cienv tags_t)
               (aenv : @aenv tags_t)
               (tenv : @tenv tags_t)
               (fenv : fenv)
               (arch : Arch.model) (s : ST.s tags_t) : result target :=
      let* inline_stmt := Inline.inline gas cienv aenv tenv fenv s in
      let* no_tup := Inline.elim_tuple inline_stmt in
      let* no_stk := Inline.elaborate_header_stacks no_tup in
      let* no_hdr := Inline.elaborate_headers no_stk in
      let* no_structs := Inline.elaborate_structs no_hdr in
      let** (gcl,_) := inline_to_gcl Ctx.initial arch no_structs in
      gcl.

  End Instr.
  End Translate.

  Module Tests.

    Variable d : tags_t.

    Definition bit (n : nat) : E.t := E.TBit (pos 4).
    Definition asm_eq (s : string) (w : nat) (r : BitVec.t) (i : tags_t) : Translate.target :=
      GCL.GAssume (leq (BitVec.BVVar s (pos w) i) r i).
    Print fold_right.
    Definition s_sequence (ss : list (ST.s tags_t)) : ST.s tags_t :=
      fold_right (fun s acc => ST.SSeq s acc d) (ST.SSkip d) ss.

    Definition ethernet_type :=
      E.THeader ([("dstAddr", bit 48);
                 ("srcAddr", bit 48);
                 ("etherType", bit 16)
                ]).

    Definition ipv4_type :=
      E.THeader ([("version", bit 4);
                 ("ihl", bit 4);
                 ("diffserv", bit 8);
                 ("totalLen", bit 16);
                 ("identification", bit 16);
                 ("flags", bit 3);
                 ("fragOffset", bit 13);
                 ("ttl", bit 8);
                 ("protocol", bit 8);
                 ("hdrChecksum", bit 16);
                 ("srcAddr", bit 32);
                 ("dstAddr", bit 32)]).

    Definition meta_type :=
      E.THeader [("do_forward", bit 1);
                ("ipv4_sa", bit 32);
                ("ipv4_da", bit 32);
                ("ipv4_sp", bit 16);
                ("ipv4_dp", bit 16);
                ("nhop_ipv4", bit 32);
                ("if_ipv4_addr", bit 32);
                ("if_mac_addr", bit 32);
                ("is_ext_if", bit 1);
                ("tcpLength", bit 16);
                ("if_index", bit 8)
                ].

    Definition tcp_type :=
      E.THeader [("srcPort", bit 16);
                ("dstPort", bit 16);
                ("seqNo", bit 32);
                ("ackNo", bit 32);
                ("dataOffset", bit 4);
                ("res", bit 4);
                ("flags", bit 8);
                ("window", bit 16);
                ("checksum", bit 16);
                ("urgentPtr", bit 16)].

    Definition std_meta_type :=
      E.THeader [("ingress_port", bit 9);
                ("egress_spec", bit 9);
                ("egress_port", bit 9);
                ("instance_type", bit 32);
                ("packet_length", bit 32);
                ("enq_timestamp", bit 32);
                ("enq_qdepth", bit 19);
                ("deq_timedelta", bit 32);
                ("deq_qdepth", bit 32);
                ("ingress_global_timestamp", bit 48);
                ("egress_global_timestamp", bit 48);
                ("mcast_grp", bit 16);
                ("egress_rid", bit 16);
                ("checksum_error", bit 1);
                ("parser_error", E.TError);
                ("priority", bit 3)].

    Definition simple_nat_ingress : (ST.s tags_t) :=
      let fwd :=
          E.EBop (E.Eq) (bit 1) (bit 1)
                 (E.EExprMember "do_forward" (bit 1) (E.EVar meta_type "meta" d) d)
                 (E.EBit (pos 1) (Zpos (pos 1)) d)
                 d
      in
      let ttl :=
          E.EBop (E.Gt) (E.TBit (pos 8)) (E.TBit (pos 8)) (E.EExprMember "ttl" (bit 8) (E.EVar ipv4_type "ipv4" d) d) (E.EBit (pos 8) Z0 d) d
      in
      let cond := E.EBop E.And E.TBool E.TBool fwd ttl d in
      ST.SSeq (ST.SInvoke "if_info" d)
              (ST.SSeq (ST.SInvoke "nat" d)
                       (ST.SConditional E.TBool
                                        cond
                                        (ST.SSeq (ST.SInvoke "ipv4_lpm" d) (ST.SInvoke "forward" d) d)
                                        (ST.SSkip d)
                                        d)
                       d)
              d.

    Locate P4cub.Control.

    Definition meta (s : string) (w : nat) :=
      E.EExprMember s (bit w) (E.EVar meta_type "meta" d) d.

    Definition std_meta (s : string) (w : nat):=
      E.EExprMember s (bit w)  (E.EVar std_meta_type "standard_metadata" d) d.

    Definition ethernet (s : string) (w : nat):=
      E.EExprMember s (bit w) (E.EVar ethernet_type "ethernet" d) d.

    Definition ipv4 (s : string) (w : nat) :=
      E.EExprMember s (bit w) (E.EVar ipv4_type "ipv4" d) d.

    Definition tcp (s : string) (w : nat) :=
      E.EExprMember s (bit w) (E.EVar tcp_type "tcp" d) d.


    Definition valid (s : string) (t : E.t) :=
      E.EUop E.IsValid E.TBool (E.EVar t s d) d.

    Definition ingress_table_env :=
      [("if_info",
        CD.Table ([(bit 8, meta "if_index" 8, E.MKExact)])
                 (["_drop"; "set_if_info"])
       );
      ("nat",
       CD.Table ([(bit 1, meta "is_ext_if" 1, E.MKExact);
                 (bit 1, valid "ipv4" ipv4_type, E.MKExact);
                 (bit 1, valid "tcp" tcp_type, E.MKExact);
                 (bit 32, ipv4 "srcAddr" 32, E.MKTernary);
                 (bit 32, ipv4 "dstAddr" 32, E.MKTernary);
                 (bit 32, tcp "srcPort" 32, E.MKTernary);
                 (bit 32, tcp "dstPort" 32, E.MKTernary)
                ])
                (["_drop";
                 "nat_miss_ext_to_int";
                 (* "nat_miss_int_to_ext"; requires generics *)
                 "nat_hit_int_to_ext";
                 "nat_hit_ext_to_int"
                 (* "nat_no_nat" *)
      ]));
      ("ipv4_lpm",
       CD.Table ([(bit 32, meta "ipv4_da" 32, E.MKLpm)])
                (["set_nhop"; "_drop"])
      );
      ("forward",
       CD.Table ([(bit 32, meta "nhop_ipv4" 32, E.MKExact)])
                (["set_dmac"; "_drop"])
      )
      ].

    Definition empty_adecl : ST.s tags_t -> adecl :=
      ADecl (Env.empty string ValEnvUtil.V.v)
            (Env.empty string fdecl)
            (Env.empty string adecl)
            (Env.empty string ARCH.P4Extern).

    Locate PAInOut.
    Definition mark_to_drop_args : E.arrowE tags_t :=
      P.Arrow [("standard_metadata", P.PAInOut (std_meta_type, E.EVar std_meta_type "standard_metadata" d))] None.

    Definition set_if_info :=
      s_sequence [ST.SAssign (bit 32) (meta "if_ipv4_addr" 32) (E.EVar (bit 32) "ipv4_addr" d) d;
                 ST.SAssign (bit 48) (meta "if_mac_addr" 48) (E.EVar (bit 48) "mac_addr" d) d;
                 ST.SAssign (bit 1) (meta "is_ext_if" 1) (E.EVar (bit 48) "is_ext" d) d].

    Definition nat_miss_ext_to_int :=
      s_sequence [ST.SAssign (bit 1) (meta "do_forward" 1) (E.EBit (pos 1) Z0 d) d;
                 ST.SExternMethodCall "v1model" "mark_to_drop" mark_to_drop_args d].

    Definition nat_hit_int_to_ext :=
      s_sequence [ST.SAssign (bit 1) (meta "do_forward" 1) (E.EBit (pos 1) (Zpos (pos 1)) d) d;
                 ST.SAssign (bit 32) (meta "ipv4_sa" 32) (E.EVar (bit 32) "srcAddr" d) d;
                 ST.SAssign (bit 32) (meta "tcp_sp" 32) (E.EVar (bit 32) "srcPort" d) d
                 ]
    .
    Definition nat_hit_ext_to_int :=
      s_sequence [ST.SAssign (bit 1) (meta "do_forward" 1) (E.EBit (pos 1) (Zpos (pos 1)) d) d;
                 ST.SAssign (bit 32) (meta "ipv4_da" 32) (E.EVar (bit 32) "dstAddr" d) d;
                 ST.SAssign (bit 32) (meta "tcp_dp" 32) (E.EVar (bit 32) "dstPort" d) d
                 ]
    .
    Definition set_dmac :=
      ST.SAssign (bit 48) (ethernet "dstAddr" 48) (E.EVar (bit 48) "dmac" d) d.

    Definition set_nhop :=
      s_sequence [ST.SAssign (bit 32) (meta "nhop_ipv4" 32) (E.EVar (bit 32) "nhop_ipv4" d) d;
                 ST.SAssign (bit 9) (std_meta "egress_spec" 9) (E.EVar (bit 9) "port" d) d;
                 ST.SAssign (bit 8) (ipv4 "ttl" 8) (E.EBop E.Minus (E.TBit (pos 8)) (E.TBit (pos 8)) (ipv4 "ttl" 8) (E.EBit (pos 8) (Zpos (pos 1)) d) d) d
                 ].

    Definition ingress_action_env :=
      [("_drop",
        empty_adecl (ST.SExternMethodCall "v1model" "mark_to_drop" mark_to_drop_args d));
      ("set_if_info", empty_adecl set_if_info);
      ("nat_miss_ext_to_int", empty_adecl nat_miss_ext_to_int);
      ("nat_hit_int_to_ext", empty_adecl nat_hit_int_to_ext);
      ("nat_hit_ext_to_int", empty_adecl nat_hit_ext_to_int);
      ("set_dmac", empty_adecl set_dmac);
      ("set_nhop", empty_adecl set_nhop)
      ].

    Print Translate.to_rvalue.

    Definition matchrow_inner (table : string) (i : tags_t) (n : nat) (elt : E.t * E.e tags_t * E.matchkind) (acc_res : result form) : result form :=
      let (te, mk) := elt in
      let (typ, exp) := te in
      let symbmatch := "_symb_" ++ table ++ "_match__" ++ string_of_nat n in
      let* acc := acc_res in
      let* w : positive := Translate.width_of_type typ in
      let* k : BitVec.t := Translate.to_rvalue exp in
      match mk with
      | E.MKExact =>
        ok (land (leq (BitVec.BVVar symbmatch w i) k i) acc i : form)
      | E.MKTernary =>
        let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
        ok (land (leq (BitVec.band (BitVec.BVVar symbmask w i) (BitVec.BVVar symbmatch w i) i)
                      (BitVec.band (BitVec.BVVar symbmask w i) k i) i)
                 acc i)
      | E.MKLpm =>
        let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
        ok (land (leq (BitVec.band (BitVec.BVVar symbmask w i) (BitVec.BVVar symbmatch w i) i)
                      (BitVec.band (BitVec.BVVar symbmask w i) k i) i)
                 acc i)
      end.

    Definition matchrow (table : string) (keys : list (E.t * E.e tags_t * E.matchkind)) (i : tags_t) : result form :=
      fold_lefti (matchrow_inner table i) (ok (LBool true i)) keys.

    Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
      let n := List.length l in
      Nat.max (PeanoNat.Nat.log2_up n) 1.

    Definition action_inner (table : string) (i : tags_t) (keys : list (E.t * E.e tags_t * E.matchkind)) (w : nat) (n : nat) (named_action : string * Translate.target) (res_acc : result Translate.target) : result Translate.target :=
      let (name, act) := named_action in
      let* matchcond := matchrow name keys i in
      let** acc := res_acc in
      g_sequence i
                 [GCL.GAssume matchcond;
                 asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BitVec.BitVec (pos 1) (pos 1) i) i;
                 asm_eq ("__symb_" ++ name ++ "_action") w  (BitVec.BitVec (pos w) (pos n) i) i;
                 act (* TODO something with action data *)].

    Definition actions_encoding (table : string) (i : tags_t) (keys : list (E.t * E.e tags_t * E.matchkind)) (actions : list (string * Translate.target)) : result Translate.target :=
      let w := bits_to_encode_list_index actions in
      fold_lefti (action_inner table i keys w) (ok (GCL.GSkip i)) actions.

    Definition instr (name : string) (i : tags_t) (keys: list (E.t * E.e tags_t * E.matchkind)) (actions: list (string * Translate.target)) : result Translate.target :=
      let** hit := actions_encoding name i keys actions in
      let miss := asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BitVec.BitVec (pos 1) (pos 1) i) i in
      GCL.GChoice hit miss.

    Definition v1model : Arch.extern :=
      [("mark_to_drop", GCL.GAssign (E.TBit (pos 1)) "standard_metadata.egress_spec" (BitVec.BitVec (pos 1) (pos 1) d) d)].

    Definition arch : Arch.model :=
      [("v1model", v1model)].

    Compute (Translate.to_rvalue (valid "ipv4" ipv4_type)).

    Compute (instr "nat" d [(bit 1, meta "is_ext_if" 1, E.MKExact);
                 (bit 1, valid "ipv4" ipv4_type, E.MKExact);
                 (bit 1, valid "tcp" tcp_type, E.MKExact);
                 (bit 32, ipv4 "srcAddr" 32, E.MKTernary);
                 (bit 32, ipv4 "dstAddr" 32, E.MKTernary);
                 (bit 32, tcp "srcPort" 32, E.MKTernary);
                 (bit 32, tcp "dstPort" 32, E.MKTernary)
                ] [("_drop", GCL.GAssign (E.TBit (pos 1)) "standard_metadata.egress_spec" (BitVec.BitVec (pos 1) (pos 1) d) d)]).

    Compute (Translate.p4cub_statement_to_gcl instr
                                              10
                                              (Env.empty string cinst)
                                              ingress_action_env
                                              ingress_table_env
                                              (Env.empty string fdecl)
                                              arch
                                              simple_nat_ingress).



  End Tests.