Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import Poulet4.P4Arith.
Require Import Poulet4.Syntax.
Require Import Poulet4.Typed.
Require Import Poulet4.P4String.
Require Import Poulet4.AList.
Require Import Poulet4.CoqLib.

Import ListNotations.


Coercion Pos.of_nat: nat >-> positive.

Module Ops.
  Section Operations.
  Context {tags_t: Type}.
  Axiom dummy_tags : tags_t.
  Definition empty_str := P4String.empty_str dummy_tags.

  Notation Val := (@ValueBase tags_t).
  Definition Fields (A : Type):= P4String.AList tags_t A.



  Definition eval_unary_op (op : OpUni) (v : Val) : option Val :=
    match op, v with
    | Not, ValBaseBool b => Some (ValBaseBool (negb b))
    | BitNot, ValBaseBit w n => Some (ValBaseBit w (BitArith.bit_not w n))
    | BitNot, ValBaseInt w n => Some (ValBaseInt w (IntArith.bit_not w n))
    | UMinus, ValBaseBit w n => Some (ValBaseBit w (BitArith.neg w n))
    | UMinus, ValBaseInt w n => Some (ValBaseInt w (IntArith.neg w n))
    | UMinus, ValBaseInteger n => Some (ValBaseInteger (- n))
    | _, _ => None
    end.


  Definition eval_binary_op_bit (op: OpBin) (w: nat) (n1 n2 : Z) : option Val :=
    match op with
    | Plus      => Some (ValBaseBit w (BitArith.plus_mod w n1 n2))
    | PlusSat   => Some (ValBaseBit w (BitArith.plus_sat w n1 n2))
    | Minus     => Some (ValBaseBit w (BitArith.minus_mod w n1 n2))
    | MinusSat  => Some (ValBaseBit w (BitArith.minus_sat w n1 n2))
    | Mul       => Some (ValBaseBit w (BitArith.mult_mod w n1 n2))
    | Le        => Some (ValBaseBool (n1 <=? n2))
    | Ge        => Some (ValBaseBool (n1 >=? n2))
    | Lt        => Some (ValBaseBool (n1 <? n2))
    | Gt        => Some (ValBaseBool (n1 >? n2))
    | BitAnd    => Some (ValBaseBit w (BitArith.bit_and w n1 n2))
    | BitXor    => Some (ValBaseBit w (BitArith.bit_xor w n1 n2))
    | BitOr     => Some (ValBaseBit w (BitArith.bit_or  w n1 n2))
    | Div       => if n2 =? 0 then None
                   else Some (ValBaseBit w (BitArith.div_mod w n1 n2))
    | Mod       => if n2 =? 0 then None
                   else Some (ValBaseBit w (BitArith.modulo_mod w n1 n2)) 
    (* implemented elsewhere *)
    | Shl | Shr | PlusPlus | Eq | NotEq
    (* not allowed *)
    | And
    | Or      => None
    end.


  Definition eval_binary_op_int (op: OpBin) (w: nat) (n1 n2 : Z) : option Val :=
    match op with
    | Plus      => Some (ValBaseInt w (IntArith.plus_mod w n1 n2))
    | PlusSat   => Some (ValBaseInt w (IntArith.plus_sat w n1 n2))
    | Minus     => Some (ValBaseInt w (IntArith.minus_mod w n1 n2))
    | MinusSat  => Some (ValBaseInt w (IntArith.minus_sat w n1 n2))
    | Mul       => Some (ValBaseInt w (IntArith.mult_mod w n1 n2))
    | Le        => Some (ValBaseBool (n1 <=? n2))
    | Ge        => Some (ValBaseBool (n1 >=? n2))
    | Lt        => Some (ValBaseBool (n1 <? n2))
    | Gt        => Some (ValBaseBool (n1 >? n2))
    | BitAnd    => Some (ValBaseInt w (IntArith.bit_and w n1 n2))
    | BitXor    => Some (ValBaseInt w (IntArith.bit_xor w n1 n2))
    | BitOr     => Some (ValBaseInt w (IntArith.bit_or  w n1 n2))
    (* implemented elsewhere *)
    | Shl | Shr | PlusPlus | Eq | NotEq
    (* not allowed *)
    | Div
    | Mod
    | And
    | Or        => None
    end.


  Definition eval_binary_op_integer (op: OpBin) (n1 n2 : Z) : option Val :=
    match op with
    | Plus      => Some (ValBaseInteger (n1 + n2))
    | Minus     => Some (ValBaseInteger (n1 - n2))
    | Mul       => Some (ValBaseInteger (n1 * n2))
    | Div       => if (n1 <? 0) || (n2 <=? 0) then None
                   else Some (ValBaseInteger (n1 / n2))
    | Mod       => if (n1 <? 0) || (n2 <=? 0) then None
                   else Some (ValBaseInteger (n1 mod n2))
    | Le        => Some (ValBaseBool (n1 <=? n2))
    | Ge        => Some (ValBaseBool (n1 >=? n2))
    | Lt        => Some (ValBaseBool (n1 <? n2))
    | Gt        => Some (ValBaseBool (n1 >? n2))
    (* implemented elsewhere *)
    | Shl | Shr | Eq | NotEq
    (* not allowed *)
    | PlusPlus
    | PlusSat
    | MinusSat
    | BitAnd
    | BitXor
    | BitOr
    | And
    | Or        => None
    end. 

  Definition eval_binary_op_bool (op: OpBin) (b1 b2: bool) : option Val :=
  match op with
  | And         => Some (ValBaseBool (andb b1 b2))
  | Or          => Some (ValBaseBool (orb b1 b2))
  | Eq | NotEq
  | _ => None
  end.

  Definition eval_binary_op_plusplus (v1 : Val) (v2 : Val) : option Val :=
    match v1, v2 with
    | ValBaseBit w1 n1, ValBaseBit w2 n2
    | ValBaseBit w1 n1, ValBaseInt w2 n2 =>
        Some (ValBaseBit (w1 + w2) (BitArith.concat w1 w2 n1 n2))
    | ValBaseInt w1 n1, ValBaseInt w2 n2
    | ValBaseInt w1 n1, ValBaseBit w2 n2 =>
        Some (ValBaseInt (w1 + w2) (IntArith.concat w1 w2 n1 n2))
    | _, _ => None
    end.

  Definition eval_binary_op_shift (op: OpBin) (v1 : Val) (v2 : Val) : option Val :=
    let arith_op :=
      match op, v1 with
      | Shl, ValBaseBit w n => 
        (fun num_bits => Some (ValBaseBit w (BitArith.shift_left w n num_bits)))
      | Shr, ValBaseBit w n =>
        (fun num_bits => Some (ValBaseBit w (BitArith.shift_right w n num_bits)))
      | Shl, ValBaseInt w n =>
        (fun num_bits => Some (ValBaseInt w (IntArith.shift_left w n num_bits)))
      | Shr, ValBaseInt w n =>
        (fun num_bits => Some (ValBaseInt w (IntArith.shift_right w n num_bits)))
      | Shl, ValBaseInteger n => 
        (fun num_bits => Some (ValBaseInteger (Z.shiftl n num_bits)))
      | Shr, ValBaseInteger n => 
        (fun num_bits => Some (ValBaseInteger (Z.shiftr n num_bits)))
      | _, _ => (fun num_bits => None)
      end in
    match v2 with
    | ValBaseBit _ n2 => arith_op n2
        (* match v1 with
        | ValBaseInteger _ => None
        | _ => arith_op n2
        end *)
    | ValBaseInteger n2 => 
        if n2 >=? 0 then arith_op n2
        else None
    | _ => None
    end.

  (* Definition sort [A] (l : Fields A) :=
    mergeSort (fun f1 f2 => string_leb (str (fst f1)) (str (fst f2))) l.

  Fixpoint sort_by_key_val (v: Val) : Val :=
    let fix sort_by_key_val' (ll : Fields Val) : Fields Val :=
      match ll with
      | nil => nil
      | (k, v) :: l' => (k, sort_by_key_val v) :: sort_by_key_val' l'
      end in
    match v with
    | ValBaseStruct l => ValBaseStruct (sort (sort_by_key_val' l))
    | ValBaseRecord l => ValBaseRecord (sort (sort_by_key_val' l))
    | ValBaseUnion l => ValBaseUnion (sort (sort_by_key_val' l))
    | ValBaseHeader l b => ValBaseHeader (sort (sort_by_key_val' l)) b
    | _ => v
    end. *)

  Fixpoint eval_binary_op_eq (v1 : Val) (v2 : Val) : option bool :=
    let fix eval_binary_op_eq_struct' (l1 l2 : Fields Val) : option bool :=
      match l1, l2 with
      | nil, nil => Some true
      | (k1, v1) :: l1', (k2, v2) :: l2' =>
        if negb (P4String.equivb k1 k2) then None
        else match eval_binary_op_eq v1 v2, eval_binary_op_eq_struct' l1' l2' with
             | Some b1, Some b2 => Some (b1 && b2)
             | _, _ => None
        end
      | _, _ => None
      end in
    let eval_binary_op_eq_struct (l1 l2 : Fields Val) : option bool :=
      if negb ((AList.key_unique l1) && (AList.key_unique l2)) then None
      else eval_binary_op_eq_struct' l1 l2 in
    let fix eval_binary_op_eq_tuple (l1 l2 : list Val): option bool :=
      match l1, l2 with
      | nil, nil => Some true
      | x1 :: l1', x2 :: l2' =>
        match eval_binary_op_eq x1 x2, eval_binary_op_eq_tuple l1' l2' with
        | Some b1, Some b2 => Some (b1 && b2)
        | _, _ => None
        end
      | _, _ => None
      end in
    match v1, v2 with
    | ValBaseError s1, ValBaseError s2 =>
        Some (P4String.equivb s1 s2)
    | ValBaseEnumField t1 s1, ValBaseEnumField t2 s2 =>
        if P4String.equivb t1 t2 then Some (P4String.equivb s1 s2)
        else None
    | ValBaseSenumField t1 s1 v1, ValBaseSenumField t2 s2 v2 =>
        if P4String.equivb t1 t2 then eval_binary_op_eq v1 v2
        else None
    | ValBaseBool b1, ValBaseBool b2 => 
        Some (eqb b1 b2)
    | ValBaseBit w1 n1, ValBaseBit w2 n2
    | ValBaseInt w1 n1, ValBaseInt w2 n2 =>
        if (w1 =? w2)%nat then Some (n1 =? n2)
        else None
    | ValBaseInteger n1, ValBaseInteger n2 => 
        Some (n1 =? n2)
    | ValBaseVarbit m1 w1 n1, ValBaseVarbit m2 w2 n2 =>
        if (m1 =? m2)%nat then Some ((w1 =? w2)%nat && (n1 =? n2))
        else None
    | ValBaseStruct l1, ValBaseStruct l2 =>
        eval_binary_op_eq_struct l1 l2
    | ValBaseRecord l1, ValBaseRecord l2 => None
        (* eval_binary_op_eq_struct l1 l2 *)
    | ValBaseUnion l1, ValBaseUnion l2 =>
        eval_binary_op_eq_struct l1 l2
    | ValBaseHeader l1 b1, ValBaseHeader l2 b2 =>
        match eval_binary_op_eq_struct l1 l2 with (* implicit type check *)
        | None => None
        | Some b3 => Some ((b1 && b2 && b3) || ((negb b1) && (negb b1)))
        end
    | ValBaseStack vs1 s1 n1, ValBaseStack vs2 s2 n2 =>
        if negb (s1 =? s2)%nat then None
        else eval_binary_op_eq_tuple vs1 vs2
    | ValBaseTuple vs1, ValBaseTuple vs2 =>
        eval_binary_op_eq_tuple vs1 vs2
    | _, _ => None
    end.

  (* Definition eval_binary_op_eq (v1 : Val) (v2 : Val) : option bool :=
    eval_binary_op_eq' (sort_by_key_val v1) (sort_by_key_val v2). *)
  
  (* 1. After implicit_cast in checker.ml, ValBaseInteger no longer exists in 
        binary operations with fixed-width bit and int.
     2. Types are checked to return None when binary operations are not allowed. *)
  Definition eval_binary_op (op: OpBin) (v1 : Val) (v2 : Val) : option Val :=
    match op, v1, v2 with
    | PlusPlus, _, _ => 
        eval_binary_op_plusplus v1 v2
    | Shl, _, _ | Shr, _, _ => 
        eval_binary_op_shift op v1 v2
    | Eq, _, _ =>
        match eval_binary_op_eq v1 v2 with
        | Some b => Some (ValBaseBool b)
        | None => None
        end
    | NotEq, _, _ =>
        match eval_binary_op_eq v1 v2 with
        | Some b => Some (ValBaseBool (negb b))
        | None => None
        end
    | _, ValBaseBit w1 n1, ValBaseBit w2 n2 => 
        if (w1 =? w2)%nat then eval_binary_op_bit op w1 n1 n2
        else None
    | _, ValBaseInt w1 n1, ValBaseInt w2 n2 => 
        if (w1 =? w2)%nat then eval_binary_op_int op w1 n1 n2
        else None
    | _, ValBaseInteger n1, ValBaseInteger n2 => 
        eval_binary_op_integer op n1 n2
    | _, ValBaseBool b1, ValBaseBool b2 =>
        eval_binary_op_bool op b1 b2
    | _, _, _ => None
    end.
  
  Definition bool_of_val (oldv : Val) : option Val :=
    match oldv with
    | ValBaseBit w n => 
      if (w =? 1)%nat then Some (ValBaseBool (n =? 1))
      else None
    | _ => None
    end.
  
  Definition bit_of_val (w : nat) (oldv : Val) : option Val :=
  match oldv with
  | ValBaseBool b => 
    if (w =? 1)%nat then Some (ValBaseBit 1 (if b then 1 else 0))
    else None
  | ValBaseInt w' n => 
      if (w =? w')%nat then Some (ValBaseBit w (BitArith.mod_bound w n))
      else None
  | ValBaseBit w' n => Some (ValBaseBit w (BitArith.mod_bound w n))
  | ValBaseInteger n => Some (ValBaseBit w (BitArith.mod_bound w n))
  | ValBaseSenumField _ _ v => 
      match v with
      | ValBaseBit w' n => if (w' =? w)%nat then Some v else None
      | _ => None
      end
  | _ => None
  end.

  Definition int_of_val (w : nat) (oldv : Val) : option Val :=
  match oldv with
  | ValBaseBit w' n =>
      if (w' =? w)%nat then Some (ValBaseInt w (IntArith.mod_bound w n))
      else None
  | ValBaseInt w' n => Some (ValBaseInt w (IntArith.mod_bound w n))
  | ValBaseInteger n => Some (ValBaseInt w (IntArith.mod_bound w n))
  | ValBaseSenumField _ _ v => 
      match v with
      | ValBaseInt w' n => if (w' =? w)%nat then Some v else None
      | _ => None
      end
  | _ => None
  end.

  (* 1. An empty field name is inserted here since the P4 manual does not specify how 
        casting to a senum assigns the field name, and multiple fields can share the same name.
        Also, the unnamed value is legal in senum, so an empty name is acceptable. 
        Lastly, the senum field name is literally unused in all semantics involving senum.
     2. Currently, casting a senum to another senum explicitly is implemented here directly.
        However, according to the manual 8.3, what should more likely happen is a implicit cast 
        from senum to its underlying type and then a explicit cast from the underlying type to
        the final senum type. However, since the implicit cast of senum is incorrect in the
        typechecker, the direct cast between senums are also implemented. *) 
  Definition enum_of_val  (name: P4String.t tags_t) (typ: option (@P4Type tags_t))
                          (members: list (P4String.t tags_t)) (oldv : Val) : option Val :=
  match typ, oldv with
  | None, _ => None
  | Some (TypBit w), ValBaseBit w' n
  | Some (TypBit w), ValBaseSenumField _ _ (ValBaseBit w' n) => 
      if (w =? w')%nat then Some (ValBaseSenumField name empty_str (ValBaseBit w n))
      else None
  | Some (TypInt w), ValBaseInt w' n
  | Some (TypInt w), ValBaseSenumField _ _ (ValBaseInt w' n) =>
      if (w =? w')%nat then Some (ValBaseSenumField name empty_str (ValBaseInt w n))
      else None
  | _, _ => None
  end.

  Fixpoint eval_cast (newtyp : @P4Type tags_t) (oldv : Val) : option Val :=
    let fix values_of_val_tuple (l1: list P4Type) 
                                (l2: list Val) : option (list Val) :=
      match l1, l2 with
      | [], [] => Some []
      | t :: l1', oldv :: l2' => 
          match eval_cast t oldv, values_of_val_tuple l1' l2' with
          | Some newv, Some l3 => Some (newv :: l3)
          | _, _ => None
          end
      | _, _ => None
      end in
    let values_of_val (l1: list P4Type) (oldv: Val) : option (list Val) :=
      match oldv with
      | ValBaseTuple l2 => values_of_val_tuple l1 l2
      | _ => None
      end in
    let fix fields_of_val_tuple (l1: Fields P4Type) 
                                (l2: list Val) : option (Fields Val) :=
      match l1, l2 with
      | [], [] => Some []
      | (k, t) :: l1', oldv :: l2' => 
          match eval_cast t oldv, fields_of_val_tuple l1' l2' with
          | Some newv, Some l3 => Some ((k, newv) :: l3)
          | _, _ => None
          end
      | _, _ => None 
      end in
    let fix fields_of_val_record (l1: Fields P4Type) 
                                 (l2: Fields Val) : option (Fields Val) :=
      match l1 with
      | [] => Some []
      | (k, t) :: l1' =>
          match AList.get l2 k with
          | None => None
          | Some oldv =>
              match eval_cast t oldv, fields_of_val_record l1' l2 with
              | Some newv, Some l3 => Some ((k, newv) :: l3)
              | _, _ => None
              end
          end
      end in
    let fields_of_val (l1: Fields P4Type) (oldv: Val) : option (Fields Val) :=
      match oldv with
      | ValBaseTuple l2 => if negb (AList.key_unique l1) then None
                           else fields_of_val_tuple l1 l2
      | ValBaseRecord l2 => if negb ((AList.key_unique l1) && (AList.key_unique l2)) then None
                            else if negb ((List.length l1) =? (List.length l2))%nat then None
                            else fields_of_val_record l1 l2
      | _ => None
      end in
    match newtyp with
    | TypBool => bool_of_val oldv
    | TypBit w => bit_of_val w oldv
    | TypInt w => int_of_val w oldv
    | TypNewType _ typ => eval_cast typ oldv
    (* Two problems with TypTypName:
       1. Need to resolve the type from the name in the Semantics.v;
       2. Need to define name_to_type such that no loop is possible. 
       eval_cast name_to_typ (name_to_typ name) oldv *)
    | TypTypeName name => None
    | TypEnum n typ mems => enum_of_val n typ mems oldv
    | TypStruct fields => 
        match fields_of_val fields oldv with
        | Some fields' => Some (ValBaseStruct fields')
        | _ => None
        end
    | TypHeader fields => 
        match fields_of_val fields oldv, oldv with
        | Some fields', ValBaseHeader _ b => Some (ValBaseHeader fields' b)
        | _, _ => None
        end
    | TypTuple types => 
        match values_of_val types oldv with
        | Some values => Some (ValBaseTuple values)
        | _ => None
        end
    | TypSet eletyp =>
        match oldv with
        | ValBaseSet v => Some (ValBaseSet v)
        | _ => match eval_cast eletyp oldv with
               | Some newv => Some (ValBaseSet (ValSetSingleton newv))
               | _ => None
               end
        end
    | _ => None
    end.
  (* Admitted. *)

  (* Fixpoint sort_by_key_typ (t: P4Type) : P4Type :=
    let fix sort_by_key_typ' (ll : Fields P4Type) : Fields P4Type :=
      match ll with
      | nil => nil
      | (k, t) :: l' => (k, sort_by_key_typ t) :: sort_by_key_typ' l'
      end in
    match t with
    | TypStruct l => TypStruct (sort (sort_by_key_typ' l))
    | TypRecord l => TypRecord (sort (sort_by_key_typ' l))
    | TypHeaderUnion l => TypHeaderUnion (sort (sort_by_key_typ' l))
    | TypHeader l => TypHeader (sort (sort_by_key_typ' l))
    | TypSet eletyp => sort_by_key_typ eletyp
    | _ => t
    end.

  Definition eval_cast (newtyp : P4Type) (oldv : Val) : option Val :=
    eval_cast' (sort_by_key_typ newtyp) (sort_by_key_val oldv). *)

  End Operations.
End Ops.
