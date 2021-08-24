Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.

Require Import Coq.Arith.EqNat.
Require Import String.
Open Scope string_scope.

Import Env.EnvNotations.

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

Definition omap {A B : Type} (f : A ->  B)  (o : option A) : option B :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Notation "'let**' p ':=' c1 'in' c2" := (omap (fun p => c2) c1)
                        (at level 61, p as pattern, c1 at next level, right associativity).

Definition liftO2 {A B C : Type} (f : A -> B -> C) (o1 : option A) (o2 : option B) : option C :=
  let* x1 := o1 in
  let** x2 := o2 in
  f x1 x2.

Definition union {A : Type} (oo : option (option A)) : option A :=
  let* o := oo in
  o.

Definition bindO2 {A B C : Type} (f : A -> B -> option C) (o1 : option A) (o2 : option B) : option C :=
  union (liftO2 f o1 o2).

Definition obindcomp {A B C : Type} (f : B -> C) (g : A -> option B) (a : A) : option C :=
  let** b := g a in
  f b.

Infix ">>=>" := obindcomp (at level 80, right associativity).

Definition ocomp {A B C : Type} (f : B -> option C) (g : A -> option B) (a : A) : option C :=
  let* b := g a in
  f b.

Infix ">=>" := ocomp (at level 80, right associativity).

Fixpoint zip {A B : Type} (xs : list A) (ys : list B) : option (list (A * B)) :=
  match xs, ys with
  | [],[] => Some []
  | [], _ => None
  | _, [] => None
  | x::xs, y::ys =>
    let** xys := zip xs ys in
    cons (x,y) xys
  end.

Fixpoint ored {A : Type} (os : list (option A)) : option (list A) :=
  match os with
  | [] => Some []
  | None :: _ => None
  | (Some x) :: os =>
    let** xs := ored os in
    x :: xs
  end.

Fixpoint fold_lefti { A B : Type } (f : nat -> A -> B -> B) (init : B) (lst : list A) : B :=
  snd (fold_left (fun '(n, b) a => (S n, f n a b)) lst (O, init)).

Definition opt_snd { A B : Type } (p : A * option B ) : option (A * B) :=
  match p with
  | (_, None) => None
  | (a, Some b) => Some (a,b)
  end.

Definition snd_opt_map {A B C : Type} (f : B -> option C) (p : A * B) : option (A * C) :=
  let (x,y) := p in
  let** z := f y in
  (x, z).

Definition union_map_snd {A B C : Type} (f : B -> option C) (xs : list (A * B)) : option (list (A * C)) :=
  ored (map (snd_opt_map f) xs).

Definition map_snd {A B C : Type} (f : B -> C) (ps : list (A * B)) : list (A * C) :=
  map (fun '(a, b) => (a, f b)) ps.

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

  Definition current (ctx : t) : option nat :=
    match ctx.(stack) with
    | [] => None
    | idx :: _ => Some idx
    end.

  Definition decr (old_ctx : t) (ctx : t)  : option (t) :=
    match ctx.(stack) with
    | [] => None
    | idx :: idxs =>
      let ctx' := {| stack := idxs;
                     used := idx :: ctx.(stack);
                     locals := old_ctx.(locals);
                     may_have_exited := old_ctx.(may_have_exited) || ctx.(may_have_exited);
                     may_have_returned := old_ctx.(may_have_returned);
                  |} in
      Some ctx'
    end.

  Definition update_exit (ctx : t) (b : bool) :=
    {| stack := ctx.(stack);
       used := ctx.(used);
       locals := ctx.(locals);
       may_have_exited := b;
       may_have_returned := ctx.(may_have_returned)
    |}.

  Definition join (tctx fctx : t) : option t :=
    if list_eq Nat.eqb tctx.(stack) fctx.(stack)
    then Some {| stack := tctx.(stack);
                 used := tctx.(used) ++ fctx.(used);
                 locals := intersect_string_list tctx.(locals) fctx.(locals);
                 may_have_exited := tctx.(may_have_exited) || fctx.(may_have_exited);
                 may_have_returned := tctx.(may_have_returned) || fctx.(may_have_returned)
              |}
    else None.

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
         | None => v
         | Some idx => scope_name v idx
         end
    else v.

End Ctx.

Definition expenv : Type := Env.t string (E.e tags_t).
Print Env.find.
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
    E.ETuple (map (subst_e η) es) i
  | E.EStruct fields i =>
    E.EStruct (F.map (fun '(t,e) => (t, subst_e η e)) fields) i
  | E.EHeader fields valid i =>
    E.EHeader (F.map (fun '(t,e) => (t, subst_e η e)) fields) (subst_e η valid) i
  | E.EExprMember mem expr_type arg i =>
    E.EExprMember mem expr_type (subst_e η arg) i
  | E.EError _ _ => e
  | E.EMatchKind _ _ => e
  | E.EHeaderStack fields headers size ni i =>
    E.EHeaderStack fields (map (subst_e η) headers) size ni i
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
      let keys' := map (fun '(t,m,k) => (t, subst_e η m, k)) keys in
      let actions' := map (fun '(s,a) => (s, fst(subst_t η a))) actions in
      (IInvoke x keys' actions' i, η)

    | IExternMethodCall extn method (P.Arrow pas returns) i =>
      let f := fun '(t,e) => (t,subst_e η e) in
      let pas' := F.map (P.paramarg_map f f) pas in
      (IExternMethodCall extn method (P.Arrow pas' returns) i, η)
    end.

  Print ST.SActCall.
  Print ST.E.args.
  Print F.fold.
  Locate In.
  Definition copy (args : ST.E.args tags_t) : expenv :=
    F.fold (fun param arg η => match arg with
                               | P.PAIn (_,e) => Env.bind param e η
                               | P.PAInOut (_,e) => Env.bind param e η
                               | P.PAOut (_,e) => Env.bind param e η
                               end)
           args (Env.empty EquivUtil.string (E.e tags_t)).

  Fixpoint inline_inner (n : nat)
             (cienv : @cienv tags_t)
             (aenv : @aenv tags_t)
             (tenv : @tenv tags_t)
             (fenv : fenv)
             (s : ST.s tags_t)
             {struct n} : option t :=
      match n with
      | 0 => None
      | S n0 =>
        match s with
        | ST.SSkip i =>
          Some (ISkip i)

        | ST.SVardecl typ x i =>
          Some (IVardecl typ x i)

        | ST.SAssign type lhs rhs i =>
          Some (IAssign type lhs rhs i)

        | ST.SConditional gtyp guard tru_blk fls_blk i =>
          let* tru_blk' := inline_inner n0 cienv aenv tenv fenv tru_blk in
          let** fls_blk' := inline_inner n0 cienv aenv tenv fenv fls_blk in
          IConditional gtyp guard tru_blk' fls_blk' i

        | ST.SSeq s1 s2 i =>
          let* i1 := inline_inner n0 cienv aenv tenv fenv s1 in
          let** i2 := inline_inner n0 cienv aenv tenv fenv s2 in
          ISeq i1 i2 i

        | ST.SBlock s =>
          let** blk := inline_inner n0 cienv aenv tenv fenv s in
          IBlock blk

        | ST.SFunCall f (P.Arrow args ret) i =>
          let* fdecl := Env.find f fenv in
          match fdecl with
          | FDecl ε fenv' body =>
            (** TODO check copy-in/copy-out *)
            let** rslt := inline_inner n0 cienv aenv tenv fenv' body in
            let η := copy args in
            IBlock rslt
          end
        | ST.SActCall a args i =>
          let* adecl := Env.find a aenv in
          match adecl with
          | ADecl ε fenv' aenv' externs body =>
            (** TODO handle copy-in/copy-out *)
            let** rslt := inline_inner n0 cienv aenv' tenv fenv' body in
            let η := copy args in
            IBlock (fst (subst_t η rslt))
          end
        | ST.SApply ci args i =>
          let* cinst := Env.find ci cienv in
          match cinst with
          | CInst closure fenv' cienv' tenv' aenv' externs' apply_blk =>
            let** rslt := inline_inner n0 cienv' aenv' tenv' fenv' apply_blk in
            (** TODO check copy-in/copy-out *)
            let η := copy args in
            IBlock (fst (subst_t η rslt))
          end

        | ST.SReturnVoid i =>
          Some (IReturnVoid i)

        | ST.SReturnFruit typ expr i =>
          Some (IReturnFruit typ expr i)

        | ST.SExit i =>
          Some (IExit i)

        | ST.SInvoke t i =>
          let* tdecl := Env.find t tenv in
          match tdecl with
          | CD.Table keys actions =>
            let act_to_gcl := fun a =>
              let* adecl := Env.find a aenv in
              match adecl with
              | ADecl _ fenv' aenv' externs body =>
                (** TODO handle copy-in/copy-out *)
                inline_inner n0 cienv aenv tenv fenv body
              end
            in
            let* acts := ored (map act_to_gcl actions) in
            let** named_acts := zip actions acts in
            IInvoke t keys named_acts i
          end

        | ST.SExternMethodCall ext method args i =>
          Some(IExternMethodCall ext method args i)
        end
      end.

  Definition inline (gas : nat) (s : ST.s tags_t) : option t :=
    inline_inner gas
                 (Env.empty EquivUtil.string cinst)
                 (Env.empty EquivUtil.string adecl)
                 (Env.empty EquivUtil.string (CD.table tags_t))
                 (Env.empty EquivUtil.string fdecl)
                 s
  .

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

    Fixpoint elim_tuple_assign (ltyp : E.t) (lhs rhs : E.e tags_t) (i : tags_t) : option Inline.t :=
      match lhs, rhs with
      | E.EVar (E.TTuple types) x i, E.ETuple es _ =>
        let** te := zip types es in
        fold_lefti (seq_tuple_elem_assign x i) (Inline.ISkip i) te
      | _,_ => Some (Inline.IAssign ltyp lhs rhs i)
      end.

    Fixpoint elim_tuple (c : Inline.t) : option t :=
      match c with
      | ISkip _ => Some c
      | IVardecl _ _ _ => Some c
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
      | IReturnVoid _ => Some c
      | IReturnFruit _ _ _ => Some c
      | IExit _ => Some c
      | IInvoke x keys actions i =>
        (** TODO do we need to eliminate tuples in keys??*)
        let opt_actions := map_snd elim_tuple actions in
        let** actions' := ored (map opt_snd opt_actions) in
        IInvoke x keys actions' i
      | IExternMethodCall _ _ _ _ =>
        (** TODO do we need to eliminate tuples in extern arguments? *)
        Some c
      end.

    (** TODO: Compiler pass to convert int<> -> bit<> *)
    Fixpoint encode_ints_as_bvs (c : Inline.t) : option Inline.t :=
      None.

    Print fold_right.



    Fixpoint header_fields (s : string) (fields : F.fs string E.t) : list (string * E.t)  :=
      F.fold (fun f typ acc => (s ++ "__f__" ++ f, typ) :: acc ) fields [(s ++ ".is_valid", E.TBool)].

    Print zip.
    (** TODO: Compiler pass to elaborate headers *)
    Search (string -> string -> bool).
    Fixpoint elaborate_headers (c : Inline.t) : option Inline.t :=
      match c with
      | ISkip _ => Some c
      | IVardecl type s i =>
        (** TODO elaborate header if type = THeader *)
        match type with
        | E.THeader fields =>
          let vars := header_fields s fields in
          let elabd_hdr_decls := fold_left (fun acc '(var_str, var_typ) => ISeq (IVardecl var_typ var_str i) acc i) vars (ISkip i) in
          Some elabd_hdr_decls
        | _ => Some c
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
            let assign_fields := fun '(lvar, ltyp) acc_opt =>
                let* acc := acc_opt in
                let** (_, rval) := F.find_value (eqb lvar) explicit_fields in
                ISeq (IAssign ltyp (E.EVar ltyp lvar il) rval i) acc i
            in
            fold_right assign_fields
                       (Some (IAssign E.TBool (E.EVar E.TBool (l ++ ".is_valid") il) valid i))
                       lvars

          | _, _ => None
          end
        | _ => Some c
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
      | IReturnVoid _ => Some c
      | IReturnFruit _ _ _ => Some c
      | IExit _ => Some c
      | IInvoke x keys actions i =>
        let opt_actions := map_snd elaborate_headers actions in
        let** actions' := ored (map opt_snd opt_actions) in
        IInvoke x keys actions' i
      | IExternMethodCall _ _ _ _ =>
        (* TODO Do we need to eliminate tuples in arguments? *)
        Some c
      end.


    Fixpoint ifold {A : Type} (n : nat) (f : nat -> A -> A) (init : A) :=
      match n with
      | O => init
      | S n' => f n (ifold n' f init)
      end.

    Search (nat -> string).
    (** TODO: Compiler pass to elaborate header stacks *)
    Fixpoint elaborate_header_stacks (c : Inline.t) : option Inline.t :=
      match c with
      | ISkip _ => Some c
      | IVardecl type x i =>
        match type with
        | E.THeaderStack fields size =>
          Some (ifold (BinPos.Pos.to_nat size)
                (fun n acc => ISeq (IVardecl (E.THeader fields) (x ++ "[" ++ string_of_nat n ++ "]") i) acc i) (ISkip i))
        | _ => Some c
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
            None
          end
        | _ => Some c
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

      | IReturnVoid _ => Some c
      | IReturnFruit _ _ _ => Some c
      | IExit _ => Some c
      | IInvoke x keys actions i =>
        (* TODO: Do something with keys? *)
        let rec_act_call := fun '(nm, act) acc_opt =>
            let* acc := acc_opt in
            let** act' := elaborate_header_stacks act in
            (nm, act') :: acc
        in
        let** actions' := fold_right rec_act_call (Some []) actions in
        IInvoke x keys actions' i
      | IExternMethodCall _ _ _ _ =>
        (* TODO: Do something with arguments? *)
        Some c
      end.

    Fixpoint struct_fields (s : string) (fields : F.fs string E.t) : list (string * E.t)  :=
      F.fold (fun f typ acc => (s ++ "__s__" ++ f, typ) :: acc ) fields [].

    (** TODO: Compiler pass to elaborate structs *)
    Fixpoint elaborate_structs (c : Inline.t) : option Inline.t :=
      match c with
      | ISkip _ => Some c
      | IVardecl type s i =>
        match type with
        | E.TStruct fields =>
          let vars := struct_fields s fields in
          let elabd_hdr_decls := fold_left (fun acc '(var_str, var_typ) => ISeq (IVardecl var_typ var_str i) acc i) vars (ISkip i) in
          Some elabd_hdr_decls
        | _ => Some c
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
                let** (_, rval) := F.find_value (eqb lvar) explicit_fields in
                ISeq (IAssign ltyp (E.EVar ltyp lvar il) rval i) acc i
            in
            fold_right assign_fields
                       (Some (ISkip i))
                       lvars

          | _, _ => None
          end
        | _ => Some c
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
      | IReturnVoid _ => Some c
      | IReturnFruit _ _ _ => Some c
      | IExit _ => Some c
      | IInvoke x keys actions i =>
        let opt_actions := map_snd elaborate_structs actions in
        let** actions' := ored (map opt_snd opt_actions) in
        IInvoke x keys actions' i
      | IExternMethodCall _ _ _ _ =>
        (* TODO Do we need to eliminate tuples in arguments? *)
        Some c
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


  (* Definition seq {lvalue rvalue : Type} (i : tags_t) (res1 res2 : (target * Ctx.t)) : target * Ctx.t := *)
  (*   let (g1, ctx1) := res1 in *)
  (*   let (g2, ctx2) := res2 in *)
  (*   let g2' := *)
  (*       if Ctx.may_have_returned ctx1 *)
  (*       then (iteb (Ctx.retvar ctx1 i) (GSkip i) g2 i) *)
  (*       else g2 in *)
  (*   let g2'' := *)
  (*       if Ctx.may_have_exited ctx1 *)
  (*       then (iteb (exit i) (GSkip i) g2 i) *)
  (*       else g2' in *)
  (*   (GSeq g1 g2'', ctx2). *)

  Module Arch.
    Definition extern : Type := Env.t string (@t string BitVec.t form).
    Definition model : Type := Env.t string extern.
    Definition find (m : model) (e f : string) : option t :=
      let* ext := Env.find e m in
      let** fn := Env.find f ext in
      fn.
  End Arch.

  Module Translate.
    Module I := Inline.
    Definition target := @t string BitVec.t form.
    Variable instr : (string -> tags_t -> list (E.t * E.e tags_t * E.matchkind) -> list (string * target) -> target).

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
        E.ETuple (map (scopify ctx) es) i
      | E.EStruct fields i =>
        E.EStruct (F.map (fun '(typ, exp) => (typ, scopify ctx exp)) fields) i
      | E.EHeader fields valid i =>
        E.EHeader (F.map (fun '(typ,exp) => (typ, scopify ctx exp)) fields) (scopify ctx valid) i
      | E.EExprMember mem expr_type arg i =>
        E.EExprMember mem expr_type (scopify ctx arg) i
      | E.EError _ _ => e
      | E.EMatchKind _ _ => e
      | E.EHeaderStack fields headers size next_index i =>
        E.EHeaderStack fields (map (scopify ctx) headers) size next_index i
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

    Search (Z -> bool).
    Print Z.
    Definition string_of_z (x : Z) :=
      if BinInt.Z.ltb x (Z0)
      then "-" ++ string_of_nat (BinInt.Z.abs_nat x)
      else string_of_nat (BinInt.Z.abs_nat x).

    Fixpoint to_lvalue (e : E.e tags_t) : option string :=
      match e with
      | E.EBool _ _ => None
      | E.EBit _ _ _ => None
      | E.EInt _ _ _ => None
      | E.EVar t x i => Some x
      | E.ESlice e τ hi lo pos =>
        (* TODO :: Allow assignment to slices *)
        None
      | E.ECast _ _ _ => None
      | E.EUop _ _ _ _ => None
      | E.EBop _ _ _ _ _ _ => None
      | E.ETuple _ _ => None
      | E.EStruct _ _ => None
      | E.EHeader _ _ _ => None
      | E.EExprMember mem expr_type arg i =>
        let** lv := to_lvalue arg in
        lv ++ "." ++ mem
      | E.EError _ _ => None
      | E.EMatchKind _ _ => None
      | E.EHeaderStack _ _ _ _ _ => None
      | E.EHeaderStackAccess stack index i =>
        let** lv := to_lvalue stack in
        (** TODO How to handle negative indices? **)
        lv ++ "["++ (string_of_z index) ++ "]"
      end.

    Definition width_of_type (t : E.t) : option positive :=
      match t with
      | E.TBool => Some (pos 1)
      | E.TBit w => Some w
      | E.TInt w =>
        (** TODO handle ints *)
        None
      | E.TError => None
      | E.TMatchKind => None
      | E.TTuple types =>
        (** TODO enumerate Tuple*)
        None
      | E.TStruct fields =>
        (** TODO enumerate fields *)
        None
      | E.THeader fields =>
        None
      | E.THeaderStack fields size =>
        None
      end.

    Definition get_header_of_stack (stack : E.e tags_t) : option E.t :=
      match stack with
      | E.EHeaderStack fields headers size next_index i =>
        Some (E.THeader fields)
      | _ => None
      end.

    Fixpoint to_rvalue (e : (E.e tags_t)) : option BitVec.t :=
      match e with
      | E.EBool b i =>
        if b
        then Some (BitVec.BitVec (pos 1) (pos 1) i)
        else Some (BitVec.BitVec (pos 0) (pos 1) i)
      | E.EBit w v i =>
        Some (BitVec.BitVec (BinInt.Z.to_pos v) w i)
      | E.EInt _ _ _ =>
        (** TODO Figure out how to handle ints *)
        None
      | E.EVar t x i =>
        let** w := width_of_type t in
        BitVec.BVVar x w i

      | E.ESlice e τ hi lo i =>
        let** rv_e := to_rvalue e in
        BitVec.UnOp (BitVec.BVSlice hi lo) rv_e i

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => Some (BitVec.UnOp (BitVec.BVCast w) rvalue_arg i) in
        match type with
        | E.TBool => cast (pos 1)
        | E.TBit w => cast w
        | E.TInt w => None (** TODO handle ints *)
        | _ =>
          (* All other casts are illegal *)
          None
        end
      | E.EUop op type arg i =>
        let* rv_arg := to_rvalue arg in
        match op with
        | E.Not => Some (BitVec.UnOp BitVec.BVNeg rv_arg i)
        | E.BitNot => Some (BitVec.UnOp BitVec.BVNeg rv_arg i)
        | E.UMinus => (* TODO handle integers *) None
        | E.IsValid =>
          let** header := to_lvalue arg in
          let hvld := header ++ ".is_valid" in
          BitVec.BVVar hvld (pos 1) i
        | E.SetValid => (* TODO @Rudy isn't this a command? *) None
        | E.SetInValid => (* TODO @Rudy -- ditto *) None
        | E.NextIndex => (* TODO Stacks *) None
        | E.Size =>  (* TODO stacks *) None
        | E.Push n => (* TODO stacks *) None
        | E.Pop n => (* TODO stacks *) None
        end
      | E.EBop op ltyp rtyp lhs rhs i =>
        let* l := to_rvalue lhs in
        let* r := to_rvalue rhs in
        let bin := fun o => Some (BitVec.BinOp o l r i) in
        match op with
        | E.Plus => bin BitVec.BVPlus
        | E.PlusSat => None (** TODO : Compiler pass to implement SatArith *)
        | E.Minus => bin BitVec.BVMinus
        | E.MinusSat => None (** TODO : Compiler pass to implement SatArith *)
        | E.Times => bin BitVec.BVTimes
        | E.Shl => bin BitVec.BVShl
        | E.Shr => bin BitVec.BVShr
        | E.Le => None
        | E.Ge => None
        | E.Lt => None
        | E.Gt => None
        | E.Eq => None
        | E.NotEq => None
        | E.BitAnd => bin BitVec.BVAnd
        | E.BitXor => bin BitVec.BVXor
        | E.BitOr => bin BitVec.BVOr
        | E.PlusPlus => bin BitVec.BVConcat
        | E.And => None
        | E.Or => None
        end
      | E.ETuple _ _ =>
        (** Should be impossible *)
        None
      | E.EStruct _ _ =>
        (** TODO: COmpiler Pass to factor out structs *)
        None
      | E.EHeader _ _ _ =>
        (* Should never have a header at this stage *)
        None
      | E.EExprMember mem expr_type arg i =>
        let* lv := to_lvalue arg in
        let** w := width_of_type expr_type in
        BitVec.BVVar lv w i
      | E.EError _ _ => None
      | E.EMatchKind _ _ => None
      | E.EHeaderStack _ _ _ _ _ =>
        (** TODO: Compiler pass to Factor Out Header Stacks*)
        None
      | E.EHeaderStackAccess stack index i =>
        (** Should be gone here *)
        None
      end.

    Definition isone (v : BitVec.t) (i :tags_t) : form :=
      LComp LEq v (BitVec.BitVec (pos 1) (pos 1) i) i.

    Fixpoint to_form (e : (E.e tags_t)) : option form :=
      match e with
      | E.EBool b i => Some (LBool b i)
      | E.EBit w v i => None
      | E.EInt _ _ _ => None
      | E.EVar t x i =>
        let* w := width_of_type t in
        if BinPos.Pos.eqb w (pos 1)
        then Some (isone (BitVec.BVVar x w i) i)
        else None

      | E.ESlice e τ hi lo i =>
        let* rv_e := to_rvalue e in
        if BinPos.Pos.eqb (BinPos.Pos.sub hi lo) (pos 1)
        then Some (isone (BitVec.UnOp (BitVec.BVSlice hi lo) rv_e i) i)
        else None

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => Some (isone (BitVec.UnOp (BitVec.BVCast w) rvalue_arg i) i) in
        match type with
        | E.TBool => cast (pos 1)
        | E.TBit w => cast w
        | E.TInt w => None (** TODO handle ints *)
        | _ =>
          (* All other casts are illegal *)
          None
        end
      | E.EUop op type arg i =>
        let* rv_arg := to_rvalue arg in
        let* w := width_of_type type in
        if negb (BinPos.Pos.eqb w (pos 1))
        then None
        else match op with
             | E.Not => Some (isone (BitVec.UnOp BitVec.BVNeg rv_arg i) i)
             | E.BitNot => Some (isone (BitVec.UnOp BitVec.BVNeg rv_arg i) i)
             | E.UMinus => (* TODO handle integers *) None
             | E.IsValid =>
               let** header := to_lvalue arg in
               let hvld := header ++ ".is_valid" in
               isone (BitVec.BVVar hvld (pos 1) i) i
             | E.SetValid => (* TODO @Rudy isn't this a command? *) None
             | E.SetInValid => (* TODO @Rudy -- ditto *) None
             | E.NextIndex => (* TODO Stacks *) None
             | E.Size =>  (* TODO stacks *) None
             | E.Push n => (* TODO stacks *) None
             | E.Pop n => (* TODO stacks *) None
             end
      | E.EBop op ltyp rtyp lhs rhs i =>
        let bbin := fun o => let* l := to_rvalue lhs in
                             let* r := to_rvalue rhs in
                             let* lw := width_of_type ltyp in
                             let* rw := width_of_type rtyp in
                             if BinPos.Pos.eqb lw (pos 1) && BinPos.Pos.eqb rw (pos 1)
                             then Some (isone (BitVec.BinOp o l r i) i)
                             else None in
        let lbin := fun o => let* l := to_form lhs in
                             let** r := to_form rhs in
                             LBop o l r i in
        let cbin := fun c => let* l := to_rvalue lhs in
                             let** r := to_rvalue rhs in
                             LComp c l r i in
        match op with
        | E.Plus => bbin BitVec.BVPlus
        | E.PlusSat => None (** TODO : Compiler pass to implement SatArith *)
        | E.Minus => bbin BitVec.BVMinus
        | E.MinusSat => None (** TODO : Compiler pass to implement SatArith *)
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
        | E.PlusPlus => None
        | E.And => lbin LAnd
        | E.Or => lbin LOr
        end
      | E.ETuple _ _ =>
        (** Should never happen *)
        None
      | E.EStruct _ _ =>
        (** TODO: COmpiler Pass to factor out Tuples *)
        None
      | E.EHeader _ _ _ =>
        (** Headers Shouldn't exist here *)
        None
      | E.EExprMember mem expr_type arg i =>
        let* lv := to_lvalue arg in
        let** w := width_of_type expr_type in
        isone (BitVec.BVVar lv w i) i
      | E.EError _ _ => None
      | E.EMatchKind _ _ => None
      | E.EHeaderStack _ _ _ _ _ =>
        None
      | E.EHeaderStackAccess stack index i =>
        None
      end.

    Definition cond (guard_type : E.t) (guard : E.e tags_t) (i : tags_t) (tres fres : (target * Ctx.t)) : option (target * Ctx.t) :=
      let (tg, tctx) := tres in
      let (fg, fctx) := fres in
      let* ctx := Ctx.join tctx fctx in
      let* phi := to_form guard in
      Some (iteb phi tg fg i, ctx).

    Fixpoint inline_to_gcl (ctx : Ctx.t) (arch : Arch.model) (s : I.t) : option (target * Ctx.t) :=
      match s with
      | I.ISkip i => Some (GSkip i, ctx)

      | I.IVardecl typ x i =>
        Some (GSkip i, Ctx.add_to_scope ctx x)

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
        let* g2 := inline_to_gcl ctx arch s2 in
        Some (seq i g1 g2)

      | I.IBlock s =>
        let* (gcl, ctx') := inline_to_gcl (Ctx.incr ctx) arch s in
        let** ctx'' := Ctx.decr ctx ctx' in
        (gcl, ctx'')

      | I.IReturnVoid i =>
        let gasn := @GAssign string BitVec.t form in
        Some (gasn (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BitVec.BitVec (pos 1) (pos 1) i) i, ctx)

      | I.IReturnFruit typ expr i =>
        (** TODO create var for return type & save it *)
        Some (GAssign (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BitVec.BitVec (pos 1) (pos 1) i) i, ctx)

      | I.IExit i =>
        Some (GAssign (E.TBit (pos 1)) "exit" (BitVec.BitVec (pos 1) (pos 1) i) i, Ctx.update_exit ctx true)

      | I.IInvoke tbl keys actions i =>
        let** actions' := union_map_snd (fst >>=> inline_to_gcl ctx arch) actions in
        let g := (instr tbl i keys actions') in
        (g, ctx)

      | I.IExternMethodCall ext method args i =>
        (** TODO handle copy-in/copy-out) *)
        let** g := Arch.find arch ext method in
        (g, ctx)
      end.

    Print cienv.
    Print Inline.elaborate_headers.
    Definition p4cub_statement_to_gcl (gas : nat) (arch : Arch.model) (s : ST.s tags_t) : option target :=
      let* inline_stmt := Inline.inline gas s in
      let* no_tup := Inline.elim_tuple inline_stmt in
      let* no_stk := Inline.elaborate_header_stacks no_tup in
      let* no_hdr := Inline.elaborate_headers no_stk in
      let* no_structs := Inline.elaborate_structs no_hdr in
      let** (gcl,_) := inline_to_gcl Ctx.initial arch no_structs in
      gcl.

End Translate.
