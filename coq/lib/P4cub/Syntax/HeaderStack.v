From Poulet4 Require Export P4cub.Syntax.AST
     P4cub.Syntax.CubNotations
     P4cub.Syntax.Auxiliary.
Require Import Coq.NArith.BinNat Coq.ZArith.BinInt.

(** In p4cub a header stack
    of size [n] and
    headers of type [ht]
    is a struct with
    0. The next index (bit<32>).
    1. The size [n] (bit<32>).
    2. The array of headers [ht]. *)
Definition
  header_stack_type
  (header_type : Typ.t) (size : N) : Typ.t :=
  Typ.Struct
    false
    [Typ.Bit 32%N;
     Typ.Bit 32%N;
     Typ.Array size header_type].

Definition
  header_stack_term
  (header_type : Typ.t) (next_index : Exp.t)
  (size : Exp.t) (headers : list Exp.t) : Exp.t :=
  Exp.Lists
    Lst.Struct
    [next_index; size;
     Exp.Lists (Lst.Array header_type) headers].

Definition
  header_stack_access
  (header_type : Typ.t) (size : N)
  (header_stack header_index : Exp.t) : Exp.t :=
  Exp.Index
    header_type
    (Exp.Member
       (Typ.Array size header_type)
       2 header_stack)
    header_index.

Definition
  header_stack_next_index
  (header_stack : Exp.t) : Exp.t :=
  Exp.Member (Typ.Bit 32%N) 0 header_stack.

Definition
  header_stack_size
  (header_stack : Exp.t) : Exp.t :=
  Exp.Member (Typ.Bit 32) 1 header_stack.

Definition
  header_stack_headers
  (header_type : Typ.t)
  (size : N) (header_stack : Exp.t) : Exp.t :=
  Exp.Member
    (Typ.Array size header_type)
    2 header_stack.
    
Definition
  header_stack_last_index
  (header_stack : Exp.t) : Exp.t :=
  Exp.Bop
    (Typ.Bit 32%N) `-%bin
    (Exp.Member (Typ.Bit 32%N) 0 header_stack)
    (32%N `W 1%Z)%exp.

(** Perhaps need indexing term in p4cub expressions? *)
Definition
  header_stack_next
  (header_type : Typ.t)
  (size : N) (header_stack : Exp.t) : Exp.t :=
  Exp.Index
    header_type
    (Exp.Member
       (Typ.Array size header_type)
       2 header_stack)
    (Exp.Member (Typ.Bit 32%N) 0 header_stack).

Definition
  header_stack_last
  (header_type : Typ.t)
  (size : N) (header_stack : Exp.t) : Exp.t :=
  Exp.Index
    header_type
    (Exp.Member
       (Typ.Array size header_type)
       2 header_stack)
    (Exp.Bop
       (Typ.Bit 32%N)
       `-%bin
       (Exp.Member (Typ.Bit 32%N) 0 header_stack)
       (32%N `W 1%Z)%exp).

Definition bit32_of_nat (n : nat) : Exp.t :=
  (32%N `W (Z.of_nat n))%exp.

Definition
  push_front
  (header_type : Typ.t) (size : N)
  (count : Z) (header_stack : Exp.t) : Stm.t :=
  let count_bit32 := (32%N `W count)%exp in
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Exp.Bop
      (Typ.Bit 32%N)
      `+%bin next_index count_bit32 in
  (* TODO: need to cap next_index by size *)
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stm in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_pushed i :=
    (hdsa i `:=
          hdsa
          (Exp.Bop
             (Typ.Bit 32%N)
             `-%bin i count_bit32))%stm in
  let asgn_front i := Stm.SetValidity false $ hdsa i in
  let asgn_pusheds :=
    seq count_nat (N.to_nat size)
        ▷ List.map bit32_of_nat
        ▷ List.map asgn_pushed in
  let asgn_fronts :=
    seq 0 count_nat
        ▷ List.map bit32_of_nat
        ▷ List.map asgn_front in
  stmt_of_list (asgn_new_next_index :: asgn_pusheds ++ asgn_fronts).

Definition
  pop_front
  (header_type : Typ.t) (size : N)
  (count : Z) (header_stack : Exp.t) : Stm.t :=
  let count_bit32 := (32%N `W count)%exp in
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Exp.Bop
      (Typ.Bit 32%N)
      `-%bin next_index count_bit32 in
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stm in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_popped i :=
    (hdsa i `:=
          hdsa
          (Exp.Bop
             (Typ.Bit 32%N) `+%bin
             i count_bit32))%stm in
  let asgn_last i := Stm.SetValidity false $ hdsa i in
  let size_nat := N.to_nat size in
  let mid :=  size_nat - count_nat in
  let asgn_poppeds :=
    seq 0 mid
        ▷ List.map bit32_of_nat
        ▷ List.map asgn_popped in
  let asgn_lasts :=
    seq mid size_nat
        ▷ List.map bit32_of_nat
        ▷ List.map asgn_last in
  stmt_of_list (asgn_new_next_index :: asgn_poppeds ++ asgn_lasts).
