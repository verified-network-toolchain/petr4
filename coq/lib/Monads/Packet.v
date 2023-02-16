Require Import Coq.Strings.String.
Require Import Poulet4.Monads.Monad.
Require Poulet4.Monads.ExceptionState.
Require Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Open Scope list_scope.

(* Corresponds to the error declarations in core.p4 relevant to parsing *)
Variant error :=
| PacketTooShort        (* Not enough bits in packet for 'extract' *)
| StackOutOfBounds      (* Reference to invalid element of a header stack. *)
| HeaderTooShort        (* Extracting too many bits into a varbit field. *)
| ParserTimeout         (* Parser execution time limit exceeded. *)
| ParserInvalidArgument (* Parser operation was called with a value
                           not supported by the implementation. *)
                        (* On bmv2, this is used to fail when extract() is
                           called with a length that is not divisible by 8.
                                                                  - Ryan *)
.

Definition error_to_string (e: error) : String.string :=
  match e with
  | PacketTooShort => "PacketTooShort"
  | StackOutOfBounds => "StackOutOfBounds"
  | HeaderTooShort => "HeaderTooShort"
  | ParserTimeout => "ParserTimeout"
  | ParserInvalidArgument => "ParserInvalidArgument"
  end.

Variant exception :=
| Reject (e: error)                    (* model-defined error to be stored in std_meta *)
| TypeError (error_msg: String.string) (* type error *)
.

Definition Packet : Type -> Type :=
  @ExceptionState.state_monad (list bool) exception.

Definition packet_ret (A: Type) (a: A) : Packet A :=
  ExceptionState.state_return a.

Definition packet_bind (A B: Type) (a: Packet A) (c: A -> Packet B) : Packet B :=
  ExceptionState.state_bind a c.

Definition err {A: Type} (e: exception) : Packet A :=
  ExceptionState.state_fail e.

#[export]
Instance PacketMonad: Monad Packet :=
  { mret := packet_ret;
    mbind := packet_bind }.

Definition verify (cond: list bool -> bool) (e: error) : Packet unit :=
  fun bs =>
    if cond bs
    then mret tt bs
    else err (Reject e) bs.

Definition pkt_min_size (n: nat) : list bool -> bool :=
  fun bs => Nat.leb n (List.length bs).

Definition extract_bits (n: nat) : Packet (list bool) :=
  verify (pkt_min_size n) PacketTooShort;;
  fun bs =>
    mret (List.firstn n bs) (List.skipn n bs).

Definition lookahead (n: nat) : Packet (list bool) :=
  verify (pkt_min_size n) PacketTooShort;;
  fun bs =>
    mret (List.firstn n bs) bs.

Definition extract_bit : Packet bool :=
  fun bs =>
    match bs with
    | b::bs => mret b bs
    | nil => err (Reject PacketTooShort) bs
    end.

Definition map_pkt (f: list bool -> list bool) : Packet unit :=
  fun bs => mret tt (f bs).

Definition emit_bits (bs : list bool) : Packet unit :=
  ExceptionState.put_state (fun pkt => pkt ++ bs).

Definition emit_bit (b : bool) : Packet unit :=
  emit_bits [b].
