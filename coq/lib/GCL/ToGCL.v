
Require Import Coq.Program.Basics.
From Poulet4 Require Export P4cub.Syntax.AST
     Utils.P4Arith Utils.Envn
     P4cub.Semantics.Dynamic.BigStep.BigStep
     Monads.Result.
Require Import Coq.Arith.EqNat String.
From Poulet4 Require Import GCL.GCL GCL.Inline Compile.ToP4cub.
Import Env.EnvNotations Result ResultNotations.
From Poulet4.Utils.Util Require Import ListUtil StringUtil.

Open Scope string_scope.
(** Compile to GCL *)
Module ST := Stm.
Module CD := Ctrl.
Module E := Exp.
Module F := F.
Module BV := GCL.BitVec.

Definition append {A : Type} (l : list A) (l' : list A) : list A :=
  match l' with
  | [] => l
  | _ =>
    List.rev_append (List.rev' l) l'
  end.

Definition fold_right {A B : Type} (f : B -> A -> A) (a0 : A) (bs : list B ) :=
  List.fold_left (fun a b => f b a) (rev' bs) a0.

Infix "@@" := String.append (right associativity, at level 60).

Section ToGCL.
  Record ctx : Type :=
    mkCtx { stack : list nat; (* The current block stack *)
            used : list nat;  (* indices that have already been used *)
            locals : list string; (* variables in the current scope *)
            may_have_exited: bool;
            may_have_returned: bool;
          }.
  (* TODO make sure that you check the variables are unique. fresh name generator based on variables that are in scope *)

  Definition initial :=
    {| stack := [0];
       used := [];
       locals := [];
       may_have_exited  := false;
       may_have_returned := false;
    |}.

  Definition incr (c : ctx) : ctx :=
    let new_idx := S(list_max (append c.(stack) c.(used))) in
    {| stack := new_idx :: c.(stack);
       used := c.(used);
       locals := [];
       may_have_exited := c.(may_have_exited);
       may_have_returned := false;
    |}.

  Definition current (c : ctx) : result string nat :=
    match c.(stack) with
    | [] => error "Tried to get context counter from empty context"
    | idx :: _ => ok idx
    end.

  Definition decr (old_ctx : ctx) (new_ctx : ctx)  : result string ctx :=
    match new_ctx.(stack) with
    | [] => error "Tried decrement empty counter"
    | idx :: idxs =>
      let ctx' := {| stack := idxs;
                     used := idx :: new_ctx.(stack);
                     locals := old_ctx.(locals);
                     may_have_exited := old_ctx.(may_have_exited) || new_ctx.(may_have_exited);
                     may_have_returned := old_ctx.(may_have_returned);
                  |} in
      ok ctx'
    end.

  Definition update_exit (c : ctx) (b : bool) :=
    {| stack := c.(stack);
       used := c.(used);
       locals := c.(locals);
       may_have_exited := b;
       may_have_returned := c.(may_have_returned)
    |}.

  Definition join (tctx fctx : ctx) : result string ctx :=
    if list_eq Nat.eqb tctx.(stack) fctx.(stack)
    then ok {| stack := tctx.(stack);
               used := append tctx.(used) fctx.(used);
               locals := intersect_string_list tctx.(locals) fctx.(locals);
               may_have_exited := tctx.(may_have_exited) || fctx.(may_have_exited);
               may_have_returned := tctx.(may_have_returned) || fctx.(may_have_returned)
            |}
    else error "Tried to join two contexts with different context counters".



  Definition retvar_name (c : ctx) : string :=
    fold_right (fun idx acc => acc @@ (string_of_nat idx)) "return" c.(stack).

  Definition retvar (c : ctx) : E.t  :=
    E.Var Typ.Bool (retvar_name c) 0.

  Definition add_to_scope (c : ctx) (v : string) :=
    {| stack := c.(stack);
       used := c.(used);
       locals := v :: c.(locals);
       may_have_exited := c.(may_have_exited);
       may_have_returned := c.(may_have_returned);
    |}.

  Definition is_local (c : ctx) (v : string) : bool :=
    string_member v (c.(locals)).

  Definition scope_name (v : string) (idx : nat) : string :=
    (* v @@ "__$__" @@ string_of_nat idx. *)
    v.


  Definition relabel_for_scope (c : ctx) (v : string) : string :=
    if is_local c v
    then match current c with
         | Error _ => v
         | Ok idx => scope_name v idx
         end
    else v.

  Definition target := @GCL.t string BV.t Form.t.

  Definition extern : Type := Env.t string target.
  (* TODO :: Think about calling out to external functions for an interpreter*)
  Definition model : Type := Env.t string extern.
  Definition find (m : model) (e f : string) : result string (GCL.t) :=
    let*~ ext := Env.find e m else "couldn't find extern " @@ e @@ " in model" in
    let*~ fn := Env.find f ext else "couldn't find field " @@ f @@ " in extern " @@ e in
    ok fn.
  Definition empty : model := Env.empty string extern.

  Definition pipeline : Type := list Typ.t -> TD.constructor_args  -> result string (ST.t * ST.t).

  Section Instr.

    Variable instr : (string -> list (nat * BitVec.t * string) -> list (string * (list BV.t * target)) -> result string target).

    Definition pos := GCL.pos.
    Fixpoint scopify (ctx : ctx) (e : E.t ) : E.t  :=
      match e with
      | E.Bool _ => e
      | E.Bit _ _ => e
      | E.Int _ _ => e
      | E.VarBit _ _ _ => e
      | E.Var typ x n =>
        let x' := relabel_for_scope ctx x in
        E.Var typ x' n
      | E.Slice hi lo e =>
        E.Slice hi lo (scopify ctx e)
      | E.Cast type arg =>
        E.Cast type (scopify ctx arg)
      | E.Uop op type arg =>
        E.Uop op type (scopify ctx arg)
      | E.Bop typ op lhs rhs =>
        E.Bop typ op (scopify ctx lhs) (scopify ctx rhs)
      | E.Lists ls es =>
        E.Lists ls (List.map (scopify ctx) es)
      | E.Member mem exp_type arg =>
        E.Member mem exp_type (scopify ctx arg)
      | E.Error _ => e
      | E.Index fs stack index =>
        E.Index fs (scopify ctx stack) (scopify ctx index)
      end.
    (**[]*)

    Definition iteb (guard : Form.t) (tru fls : target): target :=
      GCL.GChoice (GCL.GSeq (GCL.GAssume guard) tru) (GCL.GSeq (GCL.GAssume (Form.LNot guard)) fls).

    Definition seq  (res1 res2 : (target * ctx)) : target * ctx :=
      let (g1, ctx1) := res1 in
      let (g2, ctx2) := res2 in
      let g2' :=
          if may_have_returned ctx1
          then (iteb (GCL.is_true (retvar_name ctx1)) GCL.GSkip g2)
          else g2 in
      let g2'' :=
          if may_have_exited ctx1
          then iteb (Form.bveq (BV.BVVar "exit" 1) (BV.bit (Some 1) 1)) (GCL.GSkip) g2
          else g2' in
      (GCL.GSeq g1 g2'', ctx2).

    Definition string_of_z (x : Z) :=
      if BinInt.Z.ltb x (Z0)
      then "-" @@ string_of_nat (BinInt.Z.abs_nat x)
      else string_of_nat (BinInt.Z.abs_nat x).

    Definition string_of_pos (x : positive) :=
      string_of_nat (BinPosDef.Pos.to_nat x).

    Fixpoint to_lvalue (e : E.t) : result string string :=
      match e with
      | E.Bool _ => error "Boolean Literals are not lvalues"
      | E.Bit _ _ => error "BitVector Literals are not lvalues"
      | E.VarBit _ _ _ => error "Varbit Literals are not lvalues"
      | E.Int _ _ => error "Integer literals are not lvalues"
      | E.Var t x _ => ok x
      | E.Slice hi lo e =>
        (* TODO :: Allow assignment to slices *)
        error ("[FIXME] Slices ["@@ string_of_pos hi @@"," @@ string_of_pos lo @@ "] are not l-values")
      | E.Cast _ _ => error "Casts are not l-values"
      | E.Uop Typ.Bool Una.IsValid e =>
        let+ lv := to_lvalue e in
        lv @@ "." @@ "is_valid"
      | E.Uop _ _ _ => error "Unary Operations (aside from is_valid) are not l-values"
      | E.Bop _ _ _ _ => error "Binary Operations are not l-values"
      | E.Lists _ _ => error "Explicit Tuples are not l-values"
      | E.Member exp_type mem arg =>
        let+ lv := to_lvalue arg in
        lv @@ "." @@ string_of_nat mem
      | E.Error _ => error "errors are not l-values"
      | E.Index _ stack index =>
        let+ lv := to_lvalue stack in
        (** TODO How to handle negative indices? **)
        Inline.index_array_str lv 0 (* TODO: how to get nat of arbitrary index?? *)
      end.

    Definition width_of_type (x:string) (t : Typ.t) : result string nat :=
      match t with
      | Typ.Bool => ok 1
      | Typ.Bit w => ok (BinNat.N.to_nat w)
      | Typ.Int w => ok (BinPos.Pos.to_nat w)
      | Typ.VarBit w => ok (BinNat.N.to_nat w)
      | Typ.Var tx => error ("Cannot get the width of a typ variable " @@ string_of_nat tx @@ " for var " @@ x)
      | Typ.Error => ok 3 (* FIXME:: core.p4 has only 7 error codes, but this should come from a static analysis*)
      (* | Typ.MatchKind => error ("Cannot get the width of a Match Kind Type for var" @@ x) *)
      | Typ.Struct _ fields =>
        error ("Cannot get the width of a Struct Type with "@@ string_of_nat (List.length fields) @@ " for var " @@ x)
      | Typ.Array _ _ => error ("Cannot get the width of a header stack type for var" @@ x)
      end.

    Fixpoint to_header_string (e : E.t) : result string string :=
      match e with
      | E.Bool _ => error "A Boolean is not a header"
      | E.Bit _ _ => error "A bitvector literal is not a header"
      | E.Int _ _ => error "An integer literal is not a header"
      | E.VarBit _ _ _ => error "A varbit literal is not a header"
      | E.Var t x _ =>
        match t with
        | Typ.Struct _ _ => ok x
        | _ => error ("While trying to construct a string from a header, got variable " @@ x @@ ", but the type wasnt a header or struct")
        end
      | E.Slice _ _ _ => error "A Slice is not a header"
      | E.Cast _ _ => error "A Cast is not a header"
      | E.Uop _ _ _ => error "No unary operation is a header"
      | E.Bop _ _ _ _ => error "No binary operation is a header"
      | E.Lists Lst.Struct _ => error "Structs are not headers"
      | E.Lists (Lst.Header _) _ =>
        error "Header literals should not be keys"
      | E.Member exp_type mem arg =>
        let+ str := to_header_string arg in
        str @@ "." @@ string_of_nat mem
      | E.Error _ => error "errors are not header strings"
      | E.Lists (Lst.Array _) _ =>
        error "Header stacks are not headers"
      | E.Index _ stack index =>
        let+ stack_string := to_header_string stack in
        Inline.index_array_str stack_string 0 (* TODO: how to get nat from index?? *)
      end.

    Definition lookup_member_from_fields mem fields : result string Typ.t :=
      match F.find_value (String.eqb mem) fields with
      | None => error ("cannot find " @@ mem @@ "in type")
      | Some t => ok t
      end.

    Definition lookup_member_type_from_type (mem : string) (typ : Typ.t) : result string Typ.t :=
      match typ with
      | Typ.Struct _ fields =>
          lookup_member_from_fields
            mem
            (List.combine (List.map string_of_nat (List.seq 0 (List.length fields))) fields)
      | Typ.Var v =>
          error ("Error :: Type variable " @@ string_of_nat v @@ "  should've been removed")
      | _ =>
        error "don't know how to extract member from type that has no members"
      end.

    Fixpoint to_rvalue (e : E.t) : result string BV.t :=
      match e with
      | E.Bool b =>
        if b
        then ok (BV.bit (Some 1) 1)
        else ok (BV.bit (Some 1) 0)
      | E.Bit w v =>
        ok (BV.bit (Some (BinNat.N.to_nat w)) (BinInt.Z.to_nat v))
      | E.Int _ _ =>
        (** TODO Figure out how to handle ints *)
        error "[FIXME] Cannot translate signed ints to bivectors"
      | E.VarBit m w v =>
        ok (BV.bit (Some (BinNat.N.to_nat w)) (BinInt.Z.to_nat v))
      | E.Var t x _ =>
        let* w := width_of_type x t in
        ok (BV.BVVar x w)
      | E.Slice hi lo e =>
        let+ rv_e := to_rvalue e in
        (* Recall that in ToP4cub.translate_expession_pre_t we incremented the
        indices because `positive` has no 0 value *)
        BV.UnOp (BV.BVSlice ((BinPos.Pos.to_nat hi) - 1) ((BinPos.Pos.to_nat lo) - 1)) rv_e
      | E.Cast type arg =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => ok (BV.UnOp (BV.BVCast w) rvalue_arg) in
        match type with
        | Typ.Bool => cast 1
        | Typ.Bit w => cast (BinNat.N.to_nat w)
        | Typ.Int w => error "[FIXME] Signed Integers are unimplemented "
        | _ =>
          error "Illegal cast, should've been caught by the type-checker"
        end
      | E.Uop type op arg =>
        match op with
        | Una.Not =>
          let+ rv_arg := to_rvalue arg in
          BV.UnOp BV.BVNeg rv_arg
        | Una.BitNot =>
          let+ rv_arg := to_rvalue arg in
          BV.UnOp BV.BVNeg rv_arg
        | Una.Minus => error "[FIXME] Subtraction is unimplemented"
        | Una.IsValid =>
          let+ header := to_lvalue arg in
          let hvld := header @@ ".is_valid" in
          BV.BVVar hvld 1
        | Una.SetValidity b =>
            (* TODO @Rudy isn't this a command? *)
          error "SetValidity is not an expression. It should be pattern matched on earlier"
        end
      | E.Bop typ op lhs rhs =>
        let* l := to_rvalue lhs in
        let* r := to_rvalue rhs in
        let bin := fun o => ok (BV.BinOp o l r) in
        (* let* signed := *)
        (*    match typ with *)
        (*    | Typ.Bit _ => ok false *)
        (*    | Typ.Int _ => ok true *)
        (*    | _ => error "Typeerror: expected (un)signed bitvec for binary expession" *)
        (*    end *)
        (* in *)
        match op with
        | Bin.Plus =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVPlus false signed)
        | Bin.PlusSat =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVPlus true signed)
        | Bin.Minus =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVMinus false signed)
        | Bin.MinusSat =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVMinus true signed)
        | Bin.Times =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVTimes signed)
        | Bin.Shl =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVShl signed)
        | Bin.Shr =>
          let* signed :=
             match typ with
             | Typ.Bit _ => ok false
             | Typ.Int _ => ok true
             | _ => error "Typeerror: expected (un)signed bitvec for binary expession"
             end
          in
          bin (BV.BVShr signed)
        | Bin.Le => error "Typeerror: (<=) is a boolean, expected BV expession"
        | Bin.Ge => error "Typeerror: (>=) is a boolean, expected BV expession"
        | Bin.Lt => error "Typeerror: (<) is a boolean, expected BV expession"
        | Bin.Gt => error "Typeerror: (>) is a boolean, expected BV expession"
        | Bin.Eq => error "Typeerror: (=) is a boolean, expected BV expession"
        | Bin.NotEq => error "Typeerror: (!=) is a boolean, expected BV expession"
        | Bin.BitAnd => bin BV.BVAnd
        | Bin.BitXor => bin BV.BVXor
        | Bin.BitOr => bin BV.BVOr
        | Bin.PlusPlus => bin BV.BVConcat
        | Bin.And => error "Typeerror: (&&) is a boolean, expected BV expession"
        | Bin.Or => error "Typeerror: (||) is a boolean, expected BV expession"
        end
      | E.Lists Lst.Struct _ =>
        error "Structs in the rvalue position should have been factored out by previous passes"
      | E.Lists (Lst.Header _) _ =>
        error "Header in the rvalue positon should have been factored out by previous passes"
      | E.Member ret_type mem arg =>
        let* w := width_of_type (string_of_nat mem) ret_type in
        let+ lv := to_lvalue arg in
        BV.BVVar (lv @@ "." @@ string_of_nat mem) w
      | E.Error _ => error "errors are not rvalues."
      | E.Lists (Lst.Array _)  _ =>
        error "Arrays in the rvalue position should have been factored out by previous passes"
      | E.Index _ stack index =>
        error "Array indexing in the rvalue position should have been factored out by previous passes."
      end.

    Definition get_sign typ :=
       match typ with
       | Typ.Bit _ => ok false
       | Typ.Int _ => ok true
       | Typ.VarBit _ => ok false
       | Typ.Bool => error "Typerror:: expected (signed?) bitvector; got boolean"
       | Typ.Error => error "Typerror:: expected (signed?) bitvector; got error type"
       | Typ.Struct false _ => error "Typerror:: expected (signed?) bitvector; got struct type"
       | Typ.Struct true _ => error "Typerror:: expected (signed?) bitvector; got header type"
       | Typ.Array _ _ => error "Typeerror:: expected (signed?) bitvector; got array type"
       | Typ.Var _ => error "Typeerror:: expected (signed?) bitvector; got type variable"
       end.

    
    Fixpoint to_form (e : E.t) : result string Form.t :=
      match e with
      | E.Bool b => ok (Form.LBool b)
      | E.Bit _ _ =>
        error "Typeerror: Bitvector literals are not booleans (perhaps you want to insert a cast?)"
      | E.Int _ _ =>
        error "Typeerror: Signed Ints are not booleans (perhaps you want to insert a cast?)"
      | E.VarBit _ _ _ =>
        error "Typeerror: VarBit literals are not booleans (perhaps you want to insert a cast?)"
      | E.Var t x _  =>
        match t with
        | Typ.Bool => ok (Form.LVar x)
        | _ =>
          error "Typeerror: Expected a Boolean form, got something else (perhaps you want to insert a cast?)"
        end

      | E.Slice hi lo e =>
        error "Typeerror: BitVector Slices are not booleans (perhaps you want to insert a cast?)"

      | E.Error _ =>
        error "Typeerror: Errors are not formulae"
      | E.Cast type arg =>
        let~ rvalue_arg := to_rvalue arg over "couldn't convert to rvalue under cast" in
        let cast := fun w => ok (GCL.isone (BV.UnOp (BV.BVCast w) rvalue_arg)) in
        match type with
        | Typ.Bool => cast 1
        | Typ.Bit w => cast (BinNat.N.to_nat w)
        | Typ.Int w => error "[FIXME] Handle Signed Integers"
        | _ =>
          error "Invalid Cast"
        end
      | E.Uop type op arg =>
        match op with
        | Una.Not =>
          (* let~ rv_arg := to_rvalue arg over "couldn't convert to rvalue under unary operation" in *)
        (* ok (GCL.isone (BV.UnOp BV.BVNeg rv_arg)) *)
          let~ arg := to_form arg over "couldn't convert to formula under negation" in
          ok (Form.LNot arg)
        | Una.BitNot => error "Bitvector operations (!) are not booleans (perhaps you want to insert a cast?)"
        | Una.Minus => error "Saturating arithmetic (-) is not boolean (perhaps you want to insert a cast?)"
        | Una.IsValid =>
          let+ header := to_lvalue arg in
          let hvld := header @@ ".is_valid" in
          GCL.isone (BV.BVVar hvld 1)
        | Una.SetValidity b =>
          error "TODO: implement case for E.Setvalidity"
        end
      | E.Bop typ op lhs rhs =>
        let lbin := fun o => let* l := to_form lhs in
                             let* r := to_form rhs in
                             ok (Form.LBop o l r) in
        let cbin := fun o => let~ l := to_rvalue lhs over "couldn't convert left side of binary operator to rvalue " in
                             let~ r := to_rvalue rhs over "couldn't convert left side of binary operator to rvalue " in
                             ok (Form.LComp o l r) in
        let cbin_sign := fun o => let~ l := to_rvalue lhs over "couldn't convert left side of binary operator to rvalue " in
                                  let~ r := to_rvalue rhs over "couldn't convert left side of binary operator to rvalue " in
                                  let* lsign := get_sign (typ_of_exp lhs) in
                                  let* rsign := get_sign (typ_of_exp rhs) in
                                  if eqb lsign rsign then
                                    ok (Form.LComp (o lsign) l r)
                                  else
                                    error "Signedness Mismatch in comparison operator"
        in
        match op with
        | Bin.Plus => error "Typeerror: (+) is not a boolean operator"
        | Bin.PlusSat => error "Typeerror: (|+|) is not a boolean operator"
        | Bin.Minus => error "Typeerror: (-) is not a boolean operator"
        | Bin.MinusSat => error "Typeerror: (|-|) is not a boolean operator"
        | Bin.Times => error "Typerror: (*) is not a boolean operator"
        | Bin.Shl => error "Typerror: (<<) is not a boolean operator"
        | Bin.Shr => error "TYperror: (>>) is not a boolean operator"
        | Bin.Le => cbin_sign Form.LLe
        | Bin.Ge => cbin_sign Form.LGe
        | Bin.Lt => cbin_sign Form.LLt
        | Bin.Gt => cbin_sign Form.LGt
        | Bin.Eq => cbin Form.LEq
        | Bin.NotEq => cbin Form.LNeq
        | Bin.BitAnd => error "Typeerror: (&) is not a boolean operator"
        | Bin.BitXor => error "Typeerror: (^) is not a boolean operator"
        | Bin.BitOr => error "Typeerror: (|) is not a boolean operator"
        | Bin.PlusPlus => error "Typeerror: (@@) is not a boolean operator"
        | Bin.And => lbin Form.LAnd
        | Bin.Or => lbin Form.LOr
        end
      | E.Lists Lst.Struct _ =>
        error "Structs are not formulae"
      | E.Lists (Lst.Header _) _ =>
        error "Headers are not formulae"
      | E.Member exp_type mem arg =>
        let* lv := to_lvalue arg in
        (* let~ w := (width_of_type expr_type) over ("failed getting type") in *)
        let~ w := (width_of_type (string_of_nat mem) exp_type) over ("failed getting type of " @@ string_of_nat mem) in
        if Nat.eqb w 1 then
          ok (GCL.isone (BV.BVVar (lv @@ "." @@ string_of_nat mem) 1))
        else
          error ("Got type of " @@ string_of_nat mem @@ "but it's type width wasn't 1")
      | E.Lists (Lst.Array _) _ =>
        error "HeaderStacks are not formulae"
      | E.Index _ stack index =>
        error "Headers (from header stack accesses) are not formulae"
      end.

    Definition cond (guard_type : Typ.t) (guard : E.t)  (tres fres : (target * ctx)) : result string (target * ctx) :=
      let (tg, tctx) := tres in
      let (fg, fctx) := fres in
      let* ctx := join tctx fctx in
      let* phi := to_form guard in
      ok (iteb phi tg fg, ctx).

    Definition arrowE_to_arglist
      : F.fs string (paramarg E.t E.t)
        -> result string (list (string * (Form.t + BV.t))) :=
      List.fold_right (fun '(name, pa) acc_res =>
                         let* res := acc_res in
                         match pa with
                         | PAIn e
                         | PAOut e
                         | PAInOut e =>
                           match typ_of_exp e with
                           | Typ.Bool =>
                             let* phi := to_form e (*over "couldn't convert form in arrowE_to_arglist"*) in
                             ok ((name, inl phi) :: res)
                           | _ =>
                             let* e' := to_rvalue e (*over "couldn't convert rvalue in arrowE_to_arglist"*) in
                             ok ((name, inr e') :: res)
                           end
                         end)
                      (ok []).


    Definition lvalue_subst param new old :=
          if String.eqb param old then
            match new with
            | BV.BVVar new_string w =>
              new_string
            | _ =>
              (* Not sure how to substitute in anything else*)
              old
            end
          else
            old.

    Definition subst_args (g : target) (s : list (string * (Form.t + BV.t))) : result string target :=
      List.fold_right (fun '(param, arg) g_res' =>
                let+ g' := g_res' in
                match arg with
                | inl phi =>
                  GCL.subst_form (fun _ _ x => x) (fun _ _ bv => bv) Form.subst_form param phi g'
                | inr bv_exp =>
                  GCL.subst_rvalue lvalue_subst BV.subst_bv Form.subst_bv param bv_exp g'
                end) (ok g) s.

    Fixpoint inline_to_gcl (c : ctx) (arch : model) (s : Inline.t ) : result string (target * ctx) :=
      match s with
      | Inline.ISkip =>
        ok (GCL.GSkip, c)

      | Inline.IVardecl typ x =>
        ok (GCL.GSkip, add_to_scope c x)

      | Inline.IAssign type lhs rhs =>
        let~ rhs' := to_rvalue (scopify c rhs) over "couldn't convert rhs of IAssign to rvalue" in
        let~ lhs' := to_lvalue (scopify c lhs) over "couldn't convert lhs of IAssign to lvalue"  in
        let e := GCL.GAssign type lhs' rhs' in
        ok (e, c)

      | Inline.IConditional guard_type guard tru_blk fls_blk =>
        let* tru_blk' := inline_to_gcl c arch tru_blk in
        let* fls_blk' := inline_to_gcl c arch fls_blk in
        cond guard_type (scopify c guard) tru_blk' fls_blk'

      | Inline.ISeq s1 s2 =>
        let* g1 := inline_to_gcl c arch s1 in
        let+ g2 := inline_to_gcl (snd g1) arch s2 in
        seq g1 g2

      | Inline.IBlock s =>
        let* (gcl, c') := inline_to_gcl (incr c) arch s in
        let+ c'' := decr c c' in
        (gcl, c'')

      | Inline.IReturnVoid =>
        let g_asn := @GCL.GAssign string BV.t Form.t in
        ok (g_asn (Typ.Bit (BinNat.N.of_nat 1)) (retvar_name c) (BV.bit (Some 1) 1), c)

      | Inline.IReturnFruit typ exp =>
        (** TODO create var for return type & save it *)
        ok (GCL.GAssign (Typ.Bit (BinNat.N.of_nat 1)) (retvar_name c) (BV.bit (Some 1) 1), c)

      | Inline.IExit =>
        ok (GCL.GAssign (Typ.Bit (BinNat.N.of_nat 1)) "exit" (BV.bit (Some 1) 1), update_exit c true)

      | Inline.IInvoke tbl keys actions =>
        let* actions' := rred (map (fun '(name, (params, act)) =>
                                      let* bv_params := rred (List.map (fun '(name, type) =>
                                                                          let+ w := width_of_type name type in
                                                                          BV.BVVar name w) params) in
                                      let+ (gcl_act,_) := inline_to_gcl c arch act in
                                      (name, (bv_params, gcl_act))) actions)
        in
        let* keys' := rred (map (fun '(t,e,mk) =>
                                   let~ w := width_of_type "" t over ("[inline_to_gcl] failed getting width of table key. Table: " @@ tbl ) in
                                   let~ e' := to_rvalue e over "failed converting keys to rvalue" in
                                   ok (w, e', mk)) keys) in
        let+ g := instr tbl keys' actions' in
        (g, c)

      | Inline.IExternMethodCall ext method args ret =>
        (** TODO handle copy-in/copy-out) *)
          let* g := find arch ext method in
          let* gcl_args :=
            match arrowE_to_arglist args (*over "failed to convert arguments to " @@ ext @@ "." @@ method *)
            with
            | Ok o => ok o
            | Error e => error ("for " ++ method ++ " arrowE_to_arglist sad: " ++ e)
            end in
          let+ g' :=
            match subst_args g gcl_args with
            | Ok o => ok o
            | Error e => error "can't subst_args"
            end in
        (g', c)
      end.

    (* use externs to specify inter-pipeline behavior.*)
    Definition get_main ctx (pipe : pipeline) : result string (ST.t * ST.t) :=
      match find_package  ctx "main" with
      | Some (TD.Instantiate _ _ type_args args _) =>
        pipe type_args args
      | _ =>
        error "expected package, got sth else"
      end.

    Definition inlining_passes
      (gas unroll : nat) (ext : model) (ctx : ToP4cub.DeclCtx) (s : ST.t) : result string Inline.t :=
      let* inline_stm := Inline.inline gas unroll ctx s in
      let* no_stk := Inline.elaborate_arrays inline_stm in
      let* no_stk := Inline.elaborate_arrays no_stk in (*Do it twice, because extract might introduce more hss, but it wont after 2x *)
      let* no_tup := Inline.elim_tuple no_stk in
      let* no_hdr := Inline.elaborate_headers no_tup in
      let* no_structs := Inline.elaborate_structs no_hdr in
      let* no_slice := Inline.eliminate_slice_assignments no_structs in
      ok no_slice.

    Definition inline_from_p4cub (gas unroll : nat)
               (ext : model) (pipeline : pipeline)
               (ctx : ToP4cub.DeclCtx)  : result string (Inline.t * Inline.t) :=
      let* (prsr, pipe) := get_main ctx pipeline in
      let* inline_prsr := inlining_passes gas unroll ext ctx prsr in
      let+ inline_pipe := inlining_passes gas unroll ext ctx pipe in
      (inline_prsr, inline_pipe).

    Definition p4cub_statement_to_gcl
               (hdrs : bool)
               (gas unroll : nat)
               (ctx : ToP4cub.DeclCtx)
               (arch : model) (s : ST.t) : result string target :=
      let* inlined := inlining_passes gas unroll arch ctx s in
      let* instred := if hdrs then Inline.assert_headers_valid_before_use inlined else ok inlined in
      let+ (gcl,_) := inline_to_gcl initial arch instred in
      gcl.

    Definition from_p4cub (hdrs : bool) (gas unroll : nat) (ext : model) (pipe : pipeline) (ctx : ToP4cub.DeclCtx) : result string (target * target) :=
      let* (prsr, pipe) := get_main ctx pipe in
      let* tgt_prsr := p4cub_statement_to_gcl hdrs gas unroll ctx ext prsr in
      let+ tgt_pipe := p4cub_statement_to_gcl hdrs gas unroll ctx ext pipe in
      (tgt_prsr, tgt_pipe).

  End Instr.
End ToGCL.
