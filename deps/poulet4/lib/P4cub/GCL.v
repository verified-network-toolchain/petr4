Set Warnings "-custom-entry-overridden".
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

Require Import Poulet4.P4cub.Util.StringUtil.

Import Env.EnvNotations.

Import Result.
Import ResultNotations.

(** Compile to GCL *)
Module ST := Stmt.
Module CD := Control.
Module E := Expr.
Require Import Poulet4.P4cub.Inline.

Definition pos : (nat -> positive) := BinPos.Pos.of_nat.

Module BitVec.
Section BitVec.
  Variable tags_t : Type.
  Inductive bop :=
  | BVPlus (sat : bool) (signed : bool)
  | BVMinus (sat : bool) (signed : bool)
  | BVTimes (signed : bool)
  | BVConcat
  | BVShl (signed : bool)
  | BVShr (signed : bool)
  | BVAnd
  | BVOr
  | BVXor.

  Inductive uop :=
  | BVNeg
  | BVCast (i : nat)
  | BVSlice (hi lo : nat).

  Inductive t :=
  | BitVec (n : nat) (w : option nat) (i : tags_t)
  | Int (z : Z) (w : option nat) (i : tags_t)
  | BVVar (x : string) (w : nat) (i : tags_t)
  | BinOp (op : bop) (u v : t) (i : tags_t)
  | UnOp (op : uop) (v : t) (i : tags_t).

  Definition bit (w : nat) (n : nat) := BitVec n (Some w).
  Definition varbit (n : nat) := BitVec n None.
  Definition int (w : nat) (n : Z) := Int n (Some w).
  Definition integer (n : Z) := Int n None.

  Definition uadd := BinOp (BVPlus false false).
  Definition sadd := BinOp (BVPlus false true).
  Definition uadd_sat := BinOp (BVPlus true false).
  Definition sadd_sat := BinOp (BVPlus true true).

  Definition usub := BinOp (BVMinus false false).
  Definition ssub := BinOp (BVMinus false true).
  Definition usub_sat := BinOp (BVMinus true false).
  Definition ssub_sat := BinOp (BVMinus true true).

  Definition umul := BinOp (BVTimes false).
  Definition smul := BinOp (BVTimes true).

  Definition app := BinOp BVConcat.

  Definition ushl := BinOp (BVShl false).
  Definition sshl := BinOp (BVShl true).

  Definition ushr := BinOp (BVShr false).
  Definition sshr := BinOp (BVShr true).

  Definition band := BinOp BVAnd.
  Definition bor := BinOp BVOr.
  Definition bxor := BinOp BVXor.

End BitVec.
End BitVec.

Module Form.
Section Form.

  Variable tags_t : Type.


  Inductive lbop := LOr
                  | LAnd
                  | LImp
                  | LIff.

  Inductive lcomp := LEq
                   | LLe (signed : bool)
                   | LLt (signed : bool)
                   | LGe (signed : bool)
                   | LGt (signed : bool)
                   | LNeq.

  Inductive t :=
  | LBool (b : bool) (i : tags_t)
  | LBop (op : lbop) (ϕ ψ : t) (i : tags_t)
  | LNot (ϕ : t) (i : tags_t)
  | LVar (x : string) (i : tags_t)
  | LComp (comp : lcomp) (bv1 bv2 : BitVec.t tags_t) (i : tags_t).

  Definition bveq := LComp LEq.
  Definition bvule := LComp (LLe false).
  Definition bvsle := LComp (LLe true).

  Definition bvult := LComp (LLt false).
  Definition bvslt := LComp (LLt true).

  Definition bvuge := LComp (LGe false).
  Definition bvsge := LComp (LGe true).

  Definition bvugt := LComp (LGt false).
  Definition bvsgt := LComp (LGt true).

  Definition bvne := LComp LNeq.

  Definition lor := LBop LOr.
  Definition land := LBop LAnd.
  Definition limp := LBop LImp.
  Definition liff := LBop LIff.

End Form.
End Form.

Module GCL.
Section GCL.
  Variable tags_t : Type.

  Inductive t {lvalue rvalue form : Type} : Type :=
  | GSkip (i : tags_t)
  | GAssign (type : E.t) (lhs : lvalue) (rhs : rvalue) (i : tags_t)
  | GSeq (g1 g2 : t)
  | GChoice (g1 g2 : t)
  | GAssume (phi : form)
  | GAssert (phi : form)
  | GExternVoid (e : string) (args : list rvalue)
  | GExternAssn (x : string) (e : string) (args : list rvalue).

  Definition g_sequence {L R F : Type} (i : tags_t) : list (@t L R F) -> @t L R F :=
    fold_right (GSeq) (GSkip i).

  Definition is_true (x : string) (i : tags_t) : Form.t tags_t :=
    Form.bveq tags_t (BitVec.BVVar tags_t x 1 i) (BitVec.bit tags_t 1 1 i) i.

  Definition exit (i : tags_t) : Form.t tags_t := is_true "exit" i.
  Definition etrue (i : tags_t) : E.e tags_t := E.EBool true i.
  Definition efalse (i : tags_t) : E.e tags_t := E.EBool false i.
  Definition ite {lvalue rvalue : Type} (guard_type : E.t) (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop guard_type E.Not guard i)) fls).
  Definition iteb {lvalue rvalue : Type} (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.TBool E.Not guard i)) fls).

  Definition isone (v : BitVec.t tags_t) (i :tags_t) : Form.t tags_t :=
    Form.bvule tags_t v (BitVec.bit tags_t 1 1 i) i.
End GCL.
End GCL.


Module Semantics.
  Record bv := { signed : bool; val : Z; width : option nat }.

  Definition store := list (string * bv).

  Module Arch.
    Section Arch.
      Variable tags_t : Type.
      Definition impl : Type := store -> list (BitVec.t tags_t) -> (store * option bv).
      Definition t := list (string * impl).
      Fixpoint run (a : t) (s : store) (f : string) (args : list (BitVec.t tags_t)) :=
        match a with
        | [] => error ("Could not find implementation for extern " ++ f)
        | (g,impl)::a' =>
          if String.eqb g f
          then ok (impl s args)
          else run a' s f args
        end.

    End Arch.
  End Arch.

  Section Semantics.
    Variable tags_t : Type.
    Open Scope list_scope.

    Definition normalize_width (signed : bool) (z : Z) (w_u w_v : option nat) : result (bv) :=
      match w_u, w_v with
      | None, None =>
        ok {| signed := signed; val := z; width := None |}
      | Some w, Some w' =>
        if Nat.eqb w w'
        then
          let z_mod := BinInt.Z.modulo z (BinInt.Z.of_nat w) in
          ok {| signed := signed; val := z_mod; width := Some w |}
        else error "widths are different for binary op"
      | _, _ =>
        error "cannot compare signed and unsigned bvs"
      end.

    Definition apply_binop (s_op u_op : option (Z -> Z -> Z)) (u v : bv) : result bv :=
      if andb u.(signed) v.(signed)
      then
        let*~ op := s_op else "got signed bvs but no signed operation" in
        let z := op u.(val) v.(val) in
        normalize_width true z u.(width) v.(width)
      else if andb (negb u.(signed)) (negb v.(signed))
           then
             let*~ op := u_op else "got unsigned bvs but no unsigned operation" in
             let z := BinInt.Z.abs (op u.(val) v.(val)) in
             normalize_width false z u.(width) v.(width)
           else
             error "got a mixed of signed and unsigned bvs".

    Fixpoint lookup (s : store) (x : string) : result bv :=
      match s with
      | [] => error ("Could not find " ++ x ++ " in store")
      | ((y, bv)::s') =>
        if String.eqb x y
        then ok bv
        else lookup s' x
      end.

    Fixpoint remove (x : string) (s : store) : store :=
      match s with
      | [] => s
      | ((y, bv)::s') =>
        if String.eqb x y
        then s'
        else (x,bv) :: remove x s'
      end.

    Definition update (s:store) (x : string) (u : bv) : store :=
      (x, u) :: remove x s.

    Definition get_width (u v : bv) : result nat :=
      match u.(width), v.(width) with
      | Some w, Some w' =>
        if Nat.eqb w w'
        then ok w
        else error "mismatched widths"
      | None, None => error "no widths"
      |  _, _ => error "one had width the other didnt'"
      end.

    Fixpoint eval (s : store) (b : BitVec.t tags_t) : result bv :=
      match b with
      | BitVec.BitVec _ n w _ =>
        ok ({|signed := false;
              val := BinInt.Z.of_nat n;
              width := w |})

      | BitVec.Int _ z w _ =>
        ok ({|signed := true;
              val := z;
              width := w |})

      | BitVec.BVVar _ x _ _ =>
        lookup s x

      | BitVec.BinOp _ op bv1 bv2 i =>
        let* u := eval s bv1 in
        let* v := eval s bv2 in
        match op with
        | BitVec.BVPlus true _ =>
          let* w := get_width u v in
          (* |+| : int<w> -> int<w> -> int<w>*)
          let int_op := Some (IntArith.plus_sat (pos w)) in
          (* |+| : bit<w> -> bit<w> -> bit<w>*)
          let bit_op := Some (BitArith.plus_sat (BinNat.N.of_nat w)) in
          apply_binop int_op bit_op u v
        | BitVec.BVPlus false _ =>
          (* + : bit<> -> bit<> -> bit<> *)
          (* + : int<> -> int<> -> int<> *)
          let f := Some (BinInt.Z.add) in
          apply_binop f f u v
        | BitVec.BVMinus true _ =>
          let* w := get_width u v in
          (* |-| : int<w> -> int<w> -> int<w>*)
          let int_op := Some (IntArith.minus_sat (pos w)) in
          (* |-| : bit<w> -> bit<w> -> bit<w>*)
          let bit_op := Some (BitArith.minus_sat (BinNat.N.of_nat w)) in
          apply_binop int_op bit_op u v
        | BitVec.BVMinus false _ =>
          (* - : bit<> -> bit<> -> bit<> *)
          (* - : int<> -> int<> -> int<> *)
          let f := Some (BinInt.Z.add) in
          apply_binop f f u v
        | BitVec.BVTimes _ =>
          (* * : bit<> -> bit<> -> bit<> *)
          (* * : int<> -> int<> -> int<> *)
          let f := Some (BinInt.Z.mul) in
          apply_binop f f u v
        | BitVec.BVConcat =>
          match u.(width), v.(width) with
          | Some w, Some w' =>
            let+ f :=
               if andb u.(signed) v.(signed)
               then ok (IntArith.concat (Npos (pos w)) (Npos (pos w')))
               else if andb (negb u.(signed)) (negb v.(signed))
                    then ok (BitArith.concat (BinNat.N.of_nat w) (BinNat.N.of_nat w'))
                    else error "Sign Error"
            in
            let z := f u.(val) v.(val) in
            {|signed:=true; val:=z; width:= Some (w + w')|}
          | _, _ =>
            error "Cannot concatenate width-less bitvectors"
          end
        | BitVec.BVShl sg =>
          if andb (eqb sg (u.(signed))) (v.(signed)) then
            match u.(width) with
            | Some w =>
              let f := if sg
                       then IntArith.shift_left (pos w)
                       else BitArith.shift_left (BinNat.N.of_nat w) in
              ok {| signed := sg;
                    val := f u.(val) v.(val);
                    width := Some w |}
            | None =>
              ok {| signed := sg;
                    val := BinInt.Z.shiftl u.(val) v.(val);
                    width := None
                 |}
            end
          else
            error "Type error. Signedness doesn't match"
        | BitVec.BVShr sg =>
          if andb (eqb sg u.(signed)) v.(signed) then
            match u.(width) with
            | Some w =>
              let f := if sg
                       then IntArith.shift_right (pos w)
                       else BitArith.shift_right (BinNat.N.of_nat w) in
              ok {| signed := sg;
                    val := f u.(val) v.(val);
                    width := Some w |}
            | None =>
              ok {| signed := sg;
                    val := BinInt.Z.shiftr u.(val) v.(val);
                    width := None
                 |}
            end
          else
            error "Type error. Signedness doesn't match"
        | BitVec.BVAnd =>
          let f := Some (BinInt.Z.land) in
          apply_binop f f u v
        | BitVec.BVOr =>
          let f := Some BinInt.Z.lor in
          apply_binop f f u v
        | BitVec.BVXor =>
          let f := Some BinInt.Z.lxor in
          apply_binop f f u v
        end

      | BitVec.UnOp _ op bv0 i =>
        let+ u := eval s bv0 in
        match op with
        | BitVec.BVNeg =>
          if u.(signed) then
            match u.(width) with
            | Some w =>
              {| signed := true;
                 val := IntArith.bit_not (pos w) u.(val);
                 width := Some w |}
            | None =>
              {| signed := true;
                 val := BinInt.Z.lnot u.(val);
                 width := None |}
            end
          else
            match u.(width) with
            | Some w =>
              {| signed := false;
                 val := BitArith.bit_not (BinNat.N.of_nat w) u.(val);
                 width := Some w |}
            | None =>
              {| signed := false;
                 val := BinInt.Z.lnot u.(val);
                 width := None|}
            end
        | BitVec.BVCast i =>
          {| signed:= u.(signed);
             val := BinInt.Z.modulo u.(val) (Zpower.two_p (BinInt.Z.of_nat i));
             width := Some i |}
        | BitVec.BVSlice hi lo =>
          let shifted := BinInt.Z.shiftr u.(val) (BinInt.Z.of_nat lo) in
          let ones := BinInt.Z.ones (BinInt.Z.of_nat (hi - lo)) in
          let masked := BinInt.Z.land shifted ones in
           {| signed:= u.(signed);
             val := masked;
             width := Some (hi - lo) |}
        end
      end.

    Definition interp_comp (c : Form.lcomp) (x y : Z) : bool :=
      match c with
      | Form.LEq => BinInt.Z.eqb x y
      | Form.LLe _ => BinInt.Z.leb x y
      | Form.LLt _ => BinInt.Z.ltb x y
      | Form.LGe _ => BinInt.Z.geb x y
      | Form.LGt _ => BinInt.Z.gtb x y
      | Form.LNeq => negb (BinInt.Z.eqb x y)
      end.

    Fixpoint models (s : store) (phi : Form.t tags_t) : result bool :=
      match phi with
      | Form.LBool _ b _ =>
        ok b
      | Form.LBop _ op ϕ ψ _ =>
        let* a := models s ϕ in
        let+ b := models s ψ in
        match op with
        | Form.LOr => orb a b
        | Form.LAnd => andb a b
        | Form.LImp => implb a b
        | Form.LIff => eqb a b
        end
      | Form.LNot _ ϕ _ =>
        let+ a := models s ϕ in
        negb a
      | Form.LVar _ _ _ =>
        error "boolean variables unimplemented"
      | Form.LComp _ comp bv1 bv2 i =>
        let* u := eval s bv1 in
        let* v:= eval s bv2 in
        let* _ := get_width u v in
        if (eqb u.(signed) v.(signed))
        then ok (interp_comp comp u.(val) v.(val))
        else error "cannot compare signed and unsigned"
      end.

    (* translate_pipeline :: list t -> result t *)
    (* Model inter-stage behavior using GCL code (inluding externs) *)
    Fixpoint denote (a : Arch.t tags_t) (s : store) (g : @GCL.t tags_t string (BitVec.t tags_t) (Form.t tags_t)) : result (list store) :=
      match g with
      | GCL.GSkip _ _ => ok [s]
      | GCL.GAssign _ _ lhs rhs _ =>
        let+ bv := eval s rhs in
        [update s lhs bv]
      | GCL.GSeq _  g1 g2 =>
        let* ss1 := denote a s g1 in
        fold_right (fun s1 acc => let* s := denote a s1 g2 in
                                  let+ ss := acc in
                                  List.app s ss) (ok []) ss1
      | GCL.GChoice _ g1 g2 =>
        let* ss1 := denote a s g1 in
        let+ ss2 := denote a s g2 in
        List.app ss1 ss2
      | GCL.GAssume _ phi =>
        let+ b : bool := models s phi in
        if b then [s] else []
      | GCL.GAssert _ phi =>
        let* b : bool := models s phi in
        if b
        then error "Assertion Failure"
        else ok [s]
      | GCL.GExternVoid _ f args =>
        let+ (s', _) := Arch.run tags_t a s f args in
        [s']
      | GCL.GExternAssn _ x f args =>
        let* (s', ret_opt) := Arch.run tags_t a s f args in
        let*~ ret := ret_opt else "expected return value from fruitful extern" in
        ok [update s' x ret]
      end.
  End Semantics.
End Semantics.
