Require Import Monads.Monad.
Require Import Monads.State.
Require HAList.
Require Import Lists.List.
Import ListNotations.
Open Scope monad.
Require Export Coq.Strings.String.
Open Scope string_scope.
Require Import Coq.Program.Equality.
Require Import P4String.

Require Monads.Transformers.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.

Fixpoint prod (T:Set) (n:nat) : Set :=
  match n with
    | 0   => unit
    | S m => T * (prod T m)
  end.

Definition bits (n: nat) : Set := prod bool n.

Fixpoint zero_bits {n: nat} : bits n :=
  match n with
  | 0 => tt
  | S n' => (false, zero_bits)
  end.

Fixpoint one_bits {w: nat} : bits (S w) :=
  match w with
  | 0 => (true, tt)
  | S w' => (false, one_bits)
  end.

Definition bits2list {n} (bs: bits n) : list bool.
  induction n.
  - exact nil.
  - destruct bs.
    exact (b :: IHn p).
Defined.

Definition StandardMeta :=
  HAList.t [("egress_spec", bits 9)].

Record ParserState {Meta: Type} := mkParserState {
  fuel: nat;
  pkt: list bool;
  usr_meta: Meta;
  std_meta: StandardMeta
}.

Instance etaParserState {M} : Settable _ := settable! mkParserState M <fuel; pkt; usr_meta; std_meta>.

Definition Error := unit.
Definition Meta := unit.

Definition PktParser (Result: Type) := @state_monad (@ParserState Meta) Error Result.

Definition set_std_meta (f: StandardMeta -> StandardMeta) : PktParser unit :=
  put_state (fun st => st <| std_meta ::= f |>).

(* Definition skip : PktParser  *)

Definition pure {R} : R -> PktParser R := state_return.

Definition reject {R} : PktParser R := state_fail tt.

Definition next_bit : PktParser (option bool) := 
  let* st := get_state in 
  match pkt st return PktParser (option bool) with 
  | x :: pkt' => 
    put_state (fun st => st <| pkt := pkt' |>) ;;
    pure (Some x)
  | _ => pure None
  end.

Fixpoint extract_n (n: nat) : PktParser (option (bits n)) :=
  match n as n' return PktParser (option (bits n')) with
  | 0 => pure (Some tt)
  | S n' => 
    let* bits := extract_n n' in 
    let* bit := next_bit in 
    match (bit, bits) with
    | (Some bit', Some bits') => pure (Some (bit', bits'))
    | _ => pure None
    end
  end.

Definition init_meta : StandardMeta := HAList.RCons zero_bits HAList.REmp.

Definition init_state (pkt: list bool) : ParserState := 
  {| fuel := 0; pkt := pkt; usr_meta := tt; std_meta := init_meta |}.

Definition lift_option {A : Type} (x: option A) : PktParser A :=
  Transformers.lift_opt tt x.
