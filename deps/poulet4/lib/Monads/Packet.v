Require Import Poulet4.Monads.Monad.
Require Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Open Scope list_scope.

Definition Packet (A: Type) := list bool -> option A * list bool.

Definition packet_ret (A: Type) (a: A) : Packet A :=
  fun bs => (Some a, bs).

Definition packet_bind (A B: Type) (a: Packet A) (c: A -> Packet B) : Packet B :=
  fun bs =>
    let '(v, bs') := a bs in
    match v with
    | Some v => c v bs'
    | None => (None, bs')
    end.

#[export]
Instance PacketMonad: Monad Packet :=
  { mret := packet_ret;
    mbind := packet_bind }.

Definition err {A: Type} : Packet A :=
  fun bs => (None, bs).

Definition extract_bits (n: nat) : Packet (list bool) :=
  fun bs =>
    if Nat.leb (List.length bs) n
    then (Some (List.firstn n bs), List.skipn n bs)
    else err bs.

Definition lookahead (n: nat) : Packet (list bool) :=
  fun bs =>
    if Nat.leb (List.length bs) n
    then (Some (List.firstn n bs), bs)
    else err bs.

Definition extract_bit : Packet bool :=
  fun bs =>
    match bs with
    | b::bs => (Some b, bs)
    | nil => (None, bs)
    end.
