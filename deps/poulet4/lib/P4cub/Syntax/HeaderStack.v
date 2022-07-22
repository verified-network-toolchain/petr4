Require Export Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Require Import Coq.NArith.BinNat Coq.ZArith.BinInt.
Import ExprNotations StmtNotations.

(** In p4cub a header stack
    of size [n] and
    headers of type [hdr {ts}]
    is a struct with
    0. The next index (bit<32>).
    1. The size [n] (bit<32>).
    2. The array of headers [ts]
       (struct {..., struct { ts }, ...}). *)
Definition
  header_stack_type
  (header_type : list Expr.t) (size : nat) : Expr.t :=
  Expr.TStruct
    [Expr.TBit 32%N;
     Expr.TBit 32%N;
     Expr.TStruct
       (List.repeat (Expr.TStruct header_type true) size)
       false]
    false.

Definition
  header_stack_term
  (next_index : Expr.e) (size : Expr.e) (headers : list Expr.e) : Expr.e :=
  Expr.Struct
    [next_index; size; Expr.Struct headers None] None.

Definition
  header_stack_access
  (header_type : list Expr.t)
  (size index : nat) (header_stack : Expr.e) : Expr.e :=
  Expr.Member
    (Expr.TStruct header_type true)
    index
    (Expr.Member
       (Expr.TStruct
          (List.repeat (Expr.TStruct header_type true) size)
          false)
       2 header_stack).

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
  (header_type : list Expr.t)
  (size : nat) (header_stack : Expr.e) : Expr.e :=
  Expr.Member
    (Expr.TStruct
       (List.repeat
          (Expr.TStruct
             header_type true)
          size) false)
    2 header_stack.
    
Definition
  header_stack_last_index
  (header_stack : Expr.e) : Expr.e :=
  Expr.Bop
    (Expr.TBit 32%N) `-%bop
    (Expr.Member (Expr.TBit 32%N) 0 header_stack)
    (32%N `W 1%Z)%expr.

(** Perhaps need indexing term in p4cub expressions? *)
Fail Definition
     header_stack_next
     (header_type : list Expr.t)
     (size : nat) (header_stack : Expr.e) : Expr.e :=
  Expr.Member
    (Expr.TStruct header_type true)
    ((*nat value of next index of [header_stack]*)
      Expr.Member (Expr.TBit 32%N) 0 header_stack)
    (Expr.Member
       (Expr.TStruct
          (List.repeat (Expr.TStruct header_type true) size)
          false)
       2 header_stack).

Fail Definition
     header_stack_last
     (header_type : list Expr.t)
     (size : nat) (header_stack : Expr.e) : Expr.e :=
  Expr.Member
    (Expr.TStruct header_type true)
    ((*nat value of next index of [header_stack]*)
      Expr.Bop
        (Expr.TBit 32%N)
        `-%bop
        (Expr.Member (Expr.TBit 32%N) 0 header_stack)
        (32%N `W 1%Z)%expr)
    (Expr.Member
       (Expr.TStruct
          (List.repeat (Expr.TStruct header_type true) size)
          false)
       2 header_stack).

(* TODO: move to [Auxiliary.v] *)
Definition stmt_of_list : list Stmt.s -> Stmt.s :=
  List.fold_right Stmt.Seq Stmt.Skip.

Definition
  push_front
  (header_type : list Expr.t) (size : nat)
  (count : Z) (header_stack : Expr.e) : Stmt.s :=
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Expr.Bop
      (Expr.TBit 32%N)
      `+%bop next_index (32%N `W count)%expr in
  (* TODO: need to cap next_index by size *)
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stmt in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_pushed i :=
    (hdsa i `:= hdsa (i - count_nat))%stmt in
  let asgn_front i :=
    (hdsa i `:=
          Expr.Uop
          (Expr.TStruct header_type true)
          (Expr.SetValidity false)
          (hdsa i))%stmt in
  let asgn_pusheds :=
    List.map asgn_pushed (seq count_nat size) in
  let asgn_fronts :=
    List.map asgn_front (seq 0 count_nat) in
  stmt_of_list (asgn_new_next_index :: asgn_pusheds ++ asgn_fronts).

Definition
  pop_front
  (header_type : list Expr.t) (size : nat)
  (count : Z) (header_stack : Expr.e) : Stmt.s :=
  let next_index :=
    header_stack_next_index header_stack in
  let new_next_index :=
    Expr.Bop
      (Expr.TBit 32%N)
      `-%bop next_index (32%N `W count)%expr in
  let asgn_new_next_index :=
    (next_index `:= new_next_index)%stmt in
  let hdsa i :=
    header_stack_access
      header_type size i header_stack in
  let count_nat := Z.abs_nat count in
  let asgn_popped i :=
    (hdsa i `:= hdsa (i + count_nat))%stmt in
  let asgn_last i :=
    (hdsa i `:=
          Expr.Uop
          (Expr.TStruct header_type true)
          (Expr.SetValidity false)
          (hdsa i))%stmt in
  let asgn_poppeds := List.map asgn_popped (seq 0 (size - count_nat)) in
  let asgn_lasts := List.map asgn_last (seq (size - count_nat) size) in
  stmt_of_list (asgn_new_next_index :: asgn_poppeds ++ asgn_lasts).
