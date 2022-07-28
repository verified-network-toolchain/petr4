From Poulet4 Require Export P4cub.Syntax.AST
     P4cub.Syntax.CubNotations
     P4cub.Syntax.Auxiliary.
Require Import Coq.NArith.BinNat Coq.ZArith.BinInt.
Import ExprNotations StmtNotations.

(** In p4cub a header stack
    of size [n] and
    headers of type [ht]
    is a struct with
    0. The next index (bit<32>).
    1. The size [n] (bit<32>).
    2. The array of headers [ht]. *)
Definition
  header_stack_type
  (header_type : Expr.t) (size : N) : Expr.t :=
  Expr.TStruct
    false
    [Expr.TBit 32%N;
     Expr.TBit 32%N;
     Expr.TArray size header_type].

Definition
  header_stack_term
  (header_type : Expr.t) (next_index : Expr.e)
  (size : Expr.e) (headers : list Expr.e) : Expr.e :=
  Expr.Lists
    Expr.lists_struct
    [next_index; size;
     Expr.Lists (Expr.lists_array header_type) headers].

Definition
  header_stack_access
  (header_type : Expr.t) (size : N)
  (header_stack header_index : Expr.e) : Expr.e :=
  Expr.Index
    header_type
    (Expr.Member
       (Expr.TArray size header_type)
       2 header_stack)
    header_index.

Definition
  header_stack_next_index
  (header_stack : Expr.e) : Expr.e :=
  Expr.Member (Expr.TBit 32%N) 0 header_stack.

Definition
  header_stack_size
  (header_stack : Expr.e) : Expr.e :=
  Expr.Member (Expr.TBit 32) 1 header_stack.

Definition
  header_stack_headers
  (header_type : Expr.t)
  (size : N) (header_stack : Expr.e) : Expr.e :=
  Expr.Member
    (Expr.TArray size header_type)
    2 header_stack.
    
Definition
  header_stack_last_index
  (header_stack : Expr.e) : Expr.e :=
  Expr.Bop
    (Expr.TBit 32%N) `-%bop
    (Expr.Member (Expr.TBit 32%N) 0 header_stack)
    (32%N `W 1%Z)%expr.

(** Perhaps need indexing term in p4cub expressions? *)
Definition
  header_stack_next
  (header_type : Expr.t)
  (size : N) (header_stack : Expr.e) : Expr.e :=
  Expr.Index
    header_type
    (Expr.Member
       (Expr.TArray size header_type)
       2 header_stack)
    (Expr.Member (Expr.TBit 32%N) 0 header_stack).

Definition
  header_stack_last
  (header_type : Expr.t)
  (size : N) (header_stack : Expr.e) : Expr.e :=
  Expr.Index
    header_type
    (Expr.Member
       (Expr.TArray size header_type)
       2 header_stack)
    (Expr.Bop
       (Expr.TBit 32%N)
       `-%bop
       (Expr.Member (Expr.TBit 32%N) 0 header_stack)
       (32%N `W 1%Z)%expr).

Definition bit32_of_nat (n : nat) : Expr.e :=
  (32%N `W (Z.of_nat n))%expr.

Definition
  push_front
  (header_type : Expr.t) (size : N)
  (count : Z) (header_stack : Expr.e) : Stmt.s :=
  let count_bit32 := (32%N `W count)%expr in
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Expr.Bop
      (Expr.TBit 32%N)
      `+%bop next_index count_bit32 in
  (* TODO: need to cap next_index by size *)
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stmt in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_pushed i :=
    (hdsa i `:=
          hdsa
          (Expr.Bop
             (Expr.TBit 32%N)
             `-%bop i count_bit32))%stmt in
  let asgn_front i :=
    (hdsa i `:=
          Expr.Uop
          header_type
          (Expr.SetValidity false)
          (hdsa i))%stmt in
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
  (header_type : Expr.t) (size : N)
  (count : Z) (header_stack : Expr.e) : Stmt.s :=
  let count_bit32 := (32%N `W count)%expr in
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Expr.Bop
      (Expr.TBit 32%N)
      `-%bop next_index count_bit32 in
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stmt in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_popped i :=
    (hdsa i `:=
          hdsa
          (Expr.Bop
             (Expr.TBit 32%N) `+%bop
             i count_bit32))%stmt in
  let asgn_last i :=
    (hdsa i `:=
          Expr.Uop
          header_type
          (Expr.SetValidity false)
          (hdsa i))%stmt in
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
