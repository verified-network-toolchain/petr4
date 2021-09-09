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

Require Import Poulet4.P4cub.Inline.

Import Env.EnvNotations.

Import Result.
Import ResultNotations.

Import Poulet4.P4cub.Util.ListUtil.
Import Poulet4.P4cub.Util.StringUtil.

Require Import Poulet4.P4cub.GCL.


(** Compile to GCL *)
Module P := P4cub.
Module ST := P.Stmt.
Module CD := P.Control.ControlDecl.
Module E := P.Expr.
Module F := P.F.
Module BV := GCL.BitVec.

Definition tags_t : Type := Inline.tags_t.

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

Module Arch.
  Definition extern : Type := Env.t string (@GCL.t string BV.t GCL.form).
  (* TODO :: Think about calling out to external functions for an interpreter*)
  Definition model : Type := Env.t string extern.
  Definition find (m : model) (e f : string) : result GCL.t :=
    let*~ ext := Env.find e m else "couldn't find extern " ++ e ++ " in model" in
let*~ fn := Env.find f ext else "couldn't find field " ++ f ++ " in extern" in
ok fn.
  Definition empty : model := Env.empty string extern.
End Arch.

Module Translate.
  Section Instr.
    Definition target := @GCL.t string BV.t GCL.form.
    Variable instr : (string -> tags_t -> list (E.t * E.e tags_t * E.matchkind) -> list (string * target) -> result target).

    Definition pos := GCL.pos.
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

    Definition iteb (guard : GCL.form) (tru fls : target) (i : tags_t) : target :=
      GCL.GChoice (GCL.GSeq (GCL.GAssume guard) tru) (GCL.GSeq (GCL.GAssume (GCL.LNot guard i)) fls).

    Definition seq (i : tags_t) (res1 res2 : (target * Ctx.t)) : target * Ctx.t :=
      let (g1, ctx1) := res1 in
      let (g2, ctx2) := res2 in
      let g2' :=
          if Ctx.may_have_returned ctx1
          then (iteb (GCL.is_true (Ctx.retvar_name ctx1) i) (GCL.GSkip i) g2 i)
          else g2 in
      let g2'' :=
          if Ctx.may_have_exited ctx1
          then (iteb (GCL.exit i) (GCL.GSkip i) g2 i)
          else g2' in
      (GCL.GSeq g1 g2'', ctx2).

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

    Search (positive -> nat).
    Definition width_of_type (t : E.t) : result nat :=
      match t with
      | E.TBool => ok 1
      | E.TBit w => ok (BinPos.Pos.to_nat w)
      | E.TInt w => ok (BinPos.Pos.to_nat w)
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

    Search (Z -> nat).
    Fixpoint to_rvalue (e : (E.e tags_t)) : result BV.t :=
      match e with
      | E.EBool b i =>
        if b
        then ok (BV.BitVec 1 1 i)
        else ok (BV.BitVec 0 1 i)
      | E.EBit w v i =>
        ok (BV.BitVec (BinInt.Z.to_nat v) (BinPos.Pos.to_nat w) i)
      | E.EInt _ _ _ =>
        (** TODO Figure out how to handle ints *)
        error "[FIXME] Cannot translate signed ints to rvalues"
      | E.EVar t x i =>
        let** w := width_of_type t in
        BV.BVVar x w i

      | E.ESlice e τ hi lo i =>
        let** rv_e := to_rvalue e in
        BV.UnOp (BV.BVSlice (BinPos.Pos.to_nat hi) (BinPos.Pos.to_nat lo)) rv_e i

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => ok (BV.UnOp (BV.BVCast w) rvalue_arg i) in
        match type with
        | E.TBool => cast 1
        | E.TBit w => cast (BinPos.Pos.to_nat w)
        | E.TInt w => error "[FIXME] Signed Integers are unimplemented "
        | _ =>
          error "Illegal cast, should've been caught by the type-checker"
        end
      | E.EUop op type arg i =>
        match op with
        | E.Not =>
          let** rv_arg := to_rvalue arg in
          BV.UnOp BV.BVNeg rv_arg i
        | E.BitNot =>
          let** rv_arg := to_rvalue arg in
          BV.UnOp BV.BVNeg rv_arg i
        | E.UMinus => error "[FIXME] Subtraction is unimplemented"
        | E.IsValid =>
          let** header := to_header_string arg in
          let hvld := header ++ ".is_valid" in
          BV.BVVar hvld 1 i
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
        let bin := fun o => ok (BV.BinOp o l r i) in
        match op with
        | E.Plus => bin BV.BVPlus
        | E.PlusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Minus => bin BV.BVMinus
        | E.MinusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Times => bin BV.BVTimes
        | E.Shl => bin BV.BVShl
        | E.Shr => bin BV.BVShr
        | E.Le => error "Typeerror: (<=) is a boolean, expected BV expression"
        | E.Ge => error "Typeerror: (>=) is a boolean, expected BV expression"
        | E.Lt => error "Typeerror: (<) is a boolean, expected BV expression"
        | E.Gt => error "Typeerror: (>) is a boolean, expected BV expression"
        | E.Eq => error "Typeerror: (=) is a boolean, expected BV expression"
        | E.NotEq => error "Typeerror: (!=) is a boolean, expected BV expression"
        | E.BitAnd => bin BV.BVAnd
        | E.BitXor => bin BV.BVXor
        | E.BitOr => bin BV.BVOr
        | E.PlusPlus => bin BV.BVConcat
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
        BV.BVVar (lv ++ "." ++ mem) w i
      | E.EError _ _ => error "errors are not rvalues."
      | E.EMatchKind _ _ => error "MatchKinds are not rvalues"
      | E.EHeaderStack _ _ _ _ _ =>
        error "Header stacks in the rvalue position should have been factored out by previous passes"
      | E.EHeaderStackAccess stack index i =>
        error "Header stack accesses in the rvalue position should have been factored out by previous passes."
      end.

    Fixpoint to_form (e : (E.e tags_t)) : result GCL.form :=
      match e with
      | E.EBool b i => ok (GCL.LBool b i)
      | E.EBit _ _ _ =>
        error "Typeerror: Bitvector literals are not booleans (perhaps you want to insert a cast?)"
      | E.EInt _ _ _ =>
        error "Typeerror: Signed Ints are not booleans (perhaps you want to insert a cast?)"
      | E.EVar t x i =>
        match t with
        | E.TBool => ok (GCL.LVar x i)
        | _ =>
          error "Typeerror: Expected a Boolean form, got something else (perhaps you want to insert a cast?)"
        end

      | E.ESlice e τ hi lo i =>
        error "Typeerror: BitVector Slices are not booleans (perhaps you want to insert a cast?)"

      | E.ECast type arg i =>
        let* rvalue_arg := to_rvalue arg in
        let cast := fun w => ok (GCL.isone (BV.UnOp (BV.BVCast w) rvalue_arg i) i) in
        match type with
        | E.TBool => cast 1
        | E.TBit w => cast (BinPos.Pos.to_nat w)
        | E.TInt w => error "[FIXME] Handle Signed Integers"
        | _ =>
          error "Invalid Cast"
        end
      | E.EUop op type arg i =>
        let* rv_arg := to_rvalue arg in
        match op with
        | E.Not => ok (GCL.isone (BV.UnOp BV.BVNeg rv_arg i) i)
        | E.BitNot => error "Bitvector operations (!) are not booleans (perhaps you want to insert a cast?)"
        | E.UMinus => error "Saturating arithmetic (-) is not boolean (perhaps you want to insert a cast?)"
        | E.IsValid =>
          let** header := to_lvalue arg in
          let hvld := header ++ ".is_valid" in
          GCL.isone (BV.BVVar hvld 1 i) i
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
                             GCL.LBop o l r i in
        let cbin := fun c => let* l := to_rvalue lhs in
                             let** r := to_rvalue rhs in
                             GCL.LComp c l r i in
        match op with
        | E.Plus => bbin BV.BVPlus
        | E.PlusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Minus => bbin BV.BVMinus
        | E.MinusSat => error "[FIXME] Saturating Arithmetic is unimplemented"
        | E.Times => bbin BV.BVTimes
        | E.Shl => bbin BV.BVShl
        | E.Shr => bbin BV.BVShr
        | E.Le => cbin GCL.LLe
        | E.Ge => cbin GCL.LGe
        | E.Lt => cbin GCL.LLt
        | E.Gt => cbin GCL.LGt
        | E.Eq => cbin GCL.LEq
        | E.NotEq => cbin GCL.LNeq
        | E.BitAnd => bbin BV.BVAnd
        | E.BitXor => bbin BV.BVXor
        | E.BitOr => bbin BV.BVOr
        | E.PlusPlus => error "BitVector operators are not booleans (perhaps you want to insert a cast?)"
        | E.And => lbin GCL.LAnd
        | E.Or => lbin GCL.LOr
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
        ok (GCL.isone (BV.BVVar lv w i) i)
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

    Fixpoint inline_to_gcl (ctx : Ctx.t) (arch : Arch.model) (s : Inline.t) : result (target * Ctx.t) :=
      match s with
      | Inline.ISkip i =>
        ok (GCL.GSkip i, ctx)

      | Inline.IVardecl typ x i =>
        ok (GCL.GSkip i, Ctx.add_to_scope ctx x)

      | Inline.IAssign type lhs rhs i =>
        let* lhs' := to_lvalue (scopify ctx lhs) in
        let** rhs' := to_rvalue (scopify ctx rhs) in
        let e := GCL.GAssign type lhs' rhs' i in
        (e, ctx)

      | Inline.IConditional guard_type guard tru_blk fls_blk i =>
        let* tru_blk' := inline_to_gcl ctx arch tru_blk in
        let* fls_blk' := inline_to_gcl ctx arch fls_blk in
        cond guard_type (scopify ctx guard) i tru_blk' fls_blk'

      | Inline.ISeq s1 s2 i =>
        let* g1 := inline_to_gcl ctx arch s1 in
        let** g2 := inline_to_gcl (snd g1) arch s2 in
        seq i g1 g2

      | Inline.IBlock s =>
        let* (gcl, ctx') := inline_to_gcl (Ctx.incr ctx) arch s in
        let** ctx'' := Ctx.decr ctx ctx' in
        (gcl, ctx'')

      | Inline.IReturnVoid i =>
        let gasn := @GCL.GAssign string BV.t GCL.form in
        ok (gasn (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BV.BitVec 1 1 i) i, ctx)

      | Inline.IReturnFruit typ expr i =>
        (** TODO create var for return type & save it *)
        ok (GCL.GAssign (E.TBit (pos 1)) (Ctx.retvar_name ctx) (BV.BitVec 1 1 i) i, ctx)

      | Inline.IExit i =>
        ok (GCL.GAssign (E.TBit (pos 1)) "exit" (BV.BitVec 1 1 i) i, Ctx.update_exit ctx true)

      | Inline.IInvoke tbl keys actions i =>
        let* actions' := union_map_snd (fst >>=> inline_to_gcl ctx arch) actions in
        let** g := instr tbl i keys actions' in
        (g, ctx)

      | Inline.IExternMethodCall ext method args i =>
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

    Definition pos := GCL.pos.
    Definition bit (n : nat) : E.t := E.TBit (pos 4).
    Definition asm_eq (s : string) (w : nat) (r : BV.t) (i : tags_t) : Translate.target :=
      GCL.GAssume (GCL.leq (BV.BVVar s w i) r i).

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

    Definition matchrow_inner (table : string) (i : tags_t) (n : nat) (elt : E.t * E.e tags_t * E.matchkind) (acc_res : result GCL.form) : result GCL.form :=
      let (te, mk) := elt in
      let (typ, exp) := te in
      let symbmatch := "_symb_" ++ table ++ "_match__" ++ string_of_nat n in
      let* acc := acc_res in
      let* w : nat := Translate.width_of_type typ in
      let* k : BV.t := Translate.to_rvalue exp in
      match mk with
      | E.MKExact =>
        ok (GCL.land (GCL.leq (BV.BVVar symbmatch w i) k i) acc i : GCL.form)
      | E.MKTernary =>
        let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
        ok (GCL.land (GCL.leq (BV.band (BV.BVVar symbmask w i) (BV.BVVar symbmatch w i) i)
                      (BV.band (BV.BVVar symbmask w i) k i) i)
                 acc i)
      | E.MKLpm =>
        let symbmask := "symb_" ++ table ++ "_mask__" ++ string_of_nat n in
        ok (GCL.land (GCL.leq (BV.band (BV.BVVar symbmask w i) (BV.BVVar symbmatch w i) i)
                      (BV.band (BV.BVVar symbmask w i) k i) i)
                 acc i)
      end.

    Definition matchrow (table : string) (keys : list (E.t * E.e tags_t * E.matchkind)) (i : tags_t) : result GCL.form :=
      fold_lefti (matchrow_inner table i) (ok (GCL.LBool true i)) keys.

    Definition bits_to_encode_list_index {A : Type} (l : list A) : nat :=
      let n := List.length l in
      Nat.max (PeanoNat.Nat.log2_up n) 1.

    Definition action_inner (table : string) (i : tags_t) (keys : list (E.t * E.e tags_t * E.matchkind)) (w : nat) (n : nat) (named_action : string * Translate.target) (res_acc : result Translate.target) : result Translate.target :=
      let (name, act) := named_action in
      let* matchcond := matchrow name keys i in
      let** acc := res_acc in
      GCL.g_sequence i
                 [GCL.GAssume matchcond;
                 asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.BitVec 1 1 i) i;
                 asm_eq ("__symb_" ++ name ++ "_action") w  (BV.BitVec w n i) i;
                 act (* TODO something with action data *)].

    Definition actions_encoding (table : string) (i : tags_t) (keys : list (E.t * E.e tags_t * E.matchkind)) (actions : list (string * Translate.target)) : result Translate.target :=
      let w := bits_to_encode_list_index actions in
      fold_lefti (action_inner table i keys w) (ok (GCL.GSkip i)) actions.

    Definition instr (name : string) (i : tags_t) (keys: list (E.t * E.e tags_t * E.matchkind)) (actions: list (string * Translate.target)) : result Translate.target :=
      let** hit := actions_encoding name i keys actions in
      let miss := asm_eq ("__ghost_" ++ name ++ "_hit") 1 (BV.BitVec 1 1 i) i in
      GCL.GChoice hit miss.

    Definition v1model : Arch.extern :=
      [("mark_to_drop", GCL.GAssign (E.TBit (pos 1)) "standard_metadata.egress_spec" (BV.BitVec 1 1 d) d)].

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
                ] [("_drop", GCL.GAssign (E.TBit (pos 1)) "standard_metadata.egress_spec" (BV.BitVec 1 1 d) d)]).

    Compute (Translate.p4cub_statement_to_gcl instr
                                              10
                                              (Env.empty string cinst)
                                              ingress_action_env
                                              ingress_table_env
                                              (Env.empty string fdecl)
                                              arch
                                              simple_nat_ingress).


    (* This example is to test the correct implementation of scoping. *)
    (* the program itself is *)
    (*  vardecl x; x := 5; f() *)
    (* where f() := vardecl x := ipv4.src; ipv4.src := ipv4.dst; ipv4.dst := x *)
    Definition scope_occlusion_function :=
      s_sequence [
      ST.SVardecl (bit 32) "x" d;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EBit (pos 32) (Zpos (pos 5)) d) d;
      ST.SFunCall "swap" (P.Arrow [] None) d;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EVar (bit 32) "x" d) d
      ]
    .

    Definition swap_body :=
      s_sequence [
      ST.SVardecl (bit 32) "x" d;
      ST.SBlock (s_sequence [
                 ST.SVardecl (bit 32) "x" d;
                 ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (ipv4 "srcAddr" 32) d;
                 ST.SAssign (bit 32) (ipv4 "srcAddr" 32) (ipv4 "dstAddr" 32) d;
                 ST.SAssign (bit 32) (ipv4 "dstAddr" 32) (E.EVar (bit 32) "x" d) d
                 ])
      ].

    Definition swap_fdecl :=
      FDecl (Env.empty string ValEnvUtil.V.v) (Env.empty string fdecl)
            swap_body.

    Definition swap_fenv := [("swap",swap_fdecl)].

    Compute (Translate.p4cub_statement_to_gcl instr
                                              10
                                              (Env.empty string cinst)
                                              (Env.empty string adecl)
                                              (Env.empty string (CD.table tags_t))
                                              (swap_fenv)
                                              arch
                                              scope_occlusion_function).

    Print ST.SBlock.
    Definition scope_occlusion_block :=
      s_sequence [
      ST.SVardecl (bit 32) "x" d;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EBit (pos 32) (Zpos (pos 5)) d) d;
      ST.SBlock swap_body;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EVar (bit 32) "x" d) d
      ]
    .

    Compute (Translate.p4cub_statement_to_gcl instr
                                              15
                                              (Env.empty string cinst)
                                              (Env.empty string adecl)
                                              (Env.empty string (CD.table tags_t))
                                              (Env.empty string fdecl)
                                              arch
                                              scope_occlusion_block).

    Definition scope_occlusion_action :=
      s_sequence [
      ST.SVardecl (bit 32) "x" d;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EBit (pos 32) (Zpos (pos 5)) d) d;
      ST.SActCall "swap" [] d;
      ST.SActCall "swap" [] d;
      ST.SAssign (bit 32) (E.EVar (bit 32) "x" d) (E.EVar (bit 32) "x" d) d
      ]
    .

    Print ADecl.
    Print ARCH.extern_env.
    Definition swap_act :=
      ADecl (Env.empty string ValEnvUtil.V.v) (Env.empty string fdecl) (Env.empty string adecl)
            (Env.empty string ARCH.P4Extern)
            swap_body.

    Definition swap_aenv := [("swap", swap_act)].

    Compute (Translate.p4cub_statement_to_gcl instr
                                              15
                                              (Env.empty string cinst)
                                              swap_aenv
                                              (Env.empty string (CD.table tags_t))
                                              (Env.empty string fdecl)
                                              arch
                                              scope_occlusion_action).

  End Tests.
