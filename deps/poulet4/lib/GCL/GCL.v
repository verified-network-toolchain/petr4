Set Warnings "-custom-entry-overridden".
From Coq Require Import Program.Basics Arith.EqNat.
From Poulet4 Require Export P4cub.Syntax.AST
     Utils.P4Arith Utils.Envn
     P4cub.Semantics.Dynamic.BigStep.BigStep
     Monads.Result Utils.Util.StringUtil.
Require Import String.
Import Env.EnvNotations Result ResultNotations.

Open Scope string_scope.

(** Compile to GCL *)
Module ST := Stmt.
Module CD := Control.
Module E := Expr.
Require Import Poulet4.GCL.Inline.

Definition pos : (nat -> positive) := BinPos.Pos.of_nat.

Module BitVec.
Section BitVec.
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
  | BitVec (n : nat) (w : option nat)
  | Int (z : Z) (w : option nat)
  | BVVar (x : string) (w : nat)
  | BinOp (op : bop) (u v : t)
  | UnOp (op : uop) (v : t).


  Definition bit (w : option nat) (n : nat) := BitVec n w.
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

  Fixpoint subst_bv (param : string) (sub_in e: t) :=
    match e with
    | BitVec _ _ | Int _ _ => e
    | BVVar x w =>
      if String.eqb param x then
        sub_in
      else
        e
    | BinOp op u v =>
      BinOp op (subst_bv param sub_in u) (subst_bv param sub_in v)
    | UnOp op u =>
      UnOp op (subst_bv param sub_in u)
    end.

End BitVec.
End BitVec.

Module Form.
Section Form.

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
  | LBool (b : bool)
  | LBop (op : lbop) (ϕ ψ : t)
  | LNot (ϕ : t)
  | LVar (x : string)
  | LComp (comp : lcomp) (bv1 bv2 : BitVec.t).

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

  Fixpoint subst_form (param : string) (sub_in phi : t) : t :=
    match phi with
    | LBool _ | LComp _ _ _ => phi
    | LBop op phi psi =>
      LBop op (subst_form param sub_in phi) (subst_form param sub_in psi)
    | LNot phi =>
      LNot (subst_form param sub_in phi)
    | LVar x =>
      if String.eqb x param then
        sub_in
      else
        phi
    end.

  Fixpoint subst_bv (param : string) (e : BitVec.t) (phi : t) : t :=
    match phi with
    | LBool _ | LVar _ => phi
    | LComp c bv1 bv2 =>
      let bv1' := BitVec.subst_bv param e bv1 in
      let bv2' := BitVec.subst_bv param e bv2 in
      LComp c bv1' bv2'
    | LBop op phi psi =>
      LBop op (subst_bv param e phi) (subst_bv param e psi)
    | LNot phi =>
      LNot (subst_bv param e phi)
    end.

End Form.
End Form.

Module GCL.
Section GCL.
  Inductive t {lvalue rvalue form : Type} : Type :=
  | GSkip
  | GAssign (type : E.t) (lhs : lvalue) (rhs : rvalue)
  | GSeq (g1 g2 : t)
  | GChoice (g1 g2 : t)
  | GAssume (phi : form)
  | GAssert (phi : form)
  | GExternVoid (e : string) (args : list rvalue)
  | GExternAssn (x : lvalue) (e : string) (args : list rvalue)
  | GTable (tbl : string)
           (keys : list (rvalue * E.matchkind))
           (actions : list (string * t)).

  Definition g_sequence {L R F : Type} : list (@t L R F) -> @t L R F :=
    fold_right GSeq GSkip.

  Definition is_true (x : string) : Form.t :=
    Form.bveq (BitVec.BVVar x 1) (BitVec.bit (Some 1) 1).

  Definition isone (v : BitVec.t) : Form.t :=
    Form.bveq v (BitVec.bit (Some 1) 1).

  Fixpoint subst_form
           {L R F : Type}
           (l : string -> F -> L -> L) (r : string -> F -> R -> R) (f : string -> F -> F -> F)
           (param : string) (phi : F) (g : t) : t :=
    match g with
    | GSkip => GSkip
    | GAssign t x e =>
      GAssign t (l param phi x) (r param phi e)
    | GSeq g1 g2 =>
      GSeq (subst_form l r f param phi g1) (subst_form l r f param phi g2)
    | GChoice g1 g2 =>
      GChoice (subst_form l r f param phi g1) (subst_form l r f param phi g2)
    | GAssume psi =>
      GAssume (f param phi psi)
    | GAssert psi =>
      GAssert (f param phi psi)
    | GExternVoid e args =>
      GExternVoid e (List.map (r param phi) args)
    | GExternAssn x e args =>
      GExternAssn (l param phi x) e (List.map (r param phi) args)
    | GTable tbl keys actions =>
      GTable tbl (List.map (fun '(key, kind) => (r param phi key, kind)) keys)
        (List.map (fun '(x,act) => (x, subst_form l r f param phi act)) actions)
    end.

  Fixpoint subst_rvalue
           {L R F : Type}
           (l : string -> R -> L -> L) (r : string -> R -> R -> R) (f : string -> R -> F -> F)
           (param : string) (e : R) (g : t) : t :=
    match g with
    | GSkip => GSkip
    | GAssign t x e' =>
      GAssign t (l param e x) (r param e e')
    | GSeq g1 g2 =>
      GSeq (subst_rvalue l r f param e g1) (subst_rvalue l r f param e g2)
    | GChoice g1 g2 =>
      GChoice (subst_rvalue l r f param e g1) (subst_rvalue l r f param e g2)
    | GAssume psi =>
      GAssume (f param e psi)
    | GAssert psi =>
      GAssert (f param e psi)
    | GExternVoid ext args =>
      GExternVoid ext (List.map (r param e) args)
    | GExternAssn x ext args =>
      GExternAssn (l param e x) ext (List.map (r param e) args)
    | GTable x keys actions =>
      GTable x (List.map (fun '(key, kind) => (r param e key, kind)) keys)
        (List.map (fun '(x,act) => (x, subst_rvalue l r f param e act)) actions)
    end.

End GCL.
End GCL.


Module Semantics.
  Record bv := { signed : bool; val : Z; width : option nat }.

  Definition store := list (string * bv).

  Module Arch.
    Section Arch.
      Definition impl : Type := store -> list BitVec.t -> (store * option bv).
      Definition t := list (string * impl).
      Fixpoint run (a : t) (s : store) (f : string) (args : list BitVec.t) :=
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

    Fixpoint eval (s : store) (b : BitVec.t) : result bv :=
      match b with
      | BitVec.BitVec n w =>
        ok ({|signed := false;
              val := BinInt.Z.of_nat n;
              width := w |})

      | BitVec.Int z w =>
        ok ({|signed := true;
              val := z;
              width := w |})

      | BitVec.BVVar x _ =>
        lookup s x

      | BitVec.BinOp op bv1 bv2 =>
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

      | BitVec.UnOp op bv0 =>
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

    Fixpoint models (s : store) (phi : Form.t) : result bool :=
      match phi with
      | Form.LBool b =>
        ok b
      | Form.LBop op ϕ ψ =>
        let* a := models s ϕ in
        let+ b := models s ψ in
        match op with
        | Form.LOr => orb a b
        | Form.LAnd => andb a b
        | Form.LImp => implb a b
        | Form.LIff => eqb a b
        end
      | Form.LNot ϕ =>
        let+ a := models s ϕ in
        negb a
      | Form.LVar _ =>
        error "boolean variables unimplemented"
      | Form.LComp comp bv1 bv2 =>
        let* u := eval s bv1 in
        let* v:= eval s bv2 in
        let* _ := get_width u v in
        if (eqb u.(signed) v.(signed))
        then ok (interp_comp comp u.(val) v.(val))
        else error "cannot compare signed and unsigned"
      end.

    (* translate_pipeline :: list t -> result t *)
    (* Model inter-stage behavior using GCL code (inluding externs) *)
    Fixpoint denote (a : Arch.t) (s : store) (g : @GCL.t string BitVec.t Form.t) : result (list store) :=
      match g with
      | GCL.GSkip => ok [s]
      | GCL.GAssign _ lhs rhs =>
        let+ bv := eval s rhs in
        [update s lhs bv]
      | GCL.GSeq g1 g2 =>
        let* ss1 := denote a s g1 in
        fold_right (fun s1 acc => let* s := denote a s1 g2 in
                                  let+ ss := acc in
                                  List.app s ss) (ok []) ss1
      | GCL.GChoice g1 g2 =>
        let* ss1 := denote a s g1 in
        let+ ss2 := denote a s g2 in
        List.app ss1 ss2
      | GCL.GAssume phi =>
        let+ b : bool := models s phi in
        if b then [s] else []
      | GCL.GAssert phi =>
        let* b : bool := models s phi in
        if b
        then error "Assertion Failure"
        else ok [s]
      | GCL.GExternVoid f args =>
        let+ (s', _) := Arch.run a s f args in
        [s']
      | GCL.GExternAssn x f args =>
        let* (s', ret_opt) := Arch.run a s f args in
        let*~ ret := ret_opt else "expected return value from fruitful extern" in
        ok [update s' x ret]
      | GCL.GTable tbl _ _ =>
        error (String.append "No semantics for tables, found " tbl )
      end.
  End Semantics.
End Semantics.
