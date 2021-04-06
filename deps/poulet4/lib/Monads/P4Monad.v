Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.P4String.
Require Poulet4.HAList.

Require Import Coq.Lists.List.
Require Export Coq.Strings.String.
Require Import Coq.Program.Equality.
Import ListNotations.

Open Scope monad.
Open Scope string_scope.

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

Definition list2bits (xs: list bool) : bits (length xs).
induction xs.
- exact tt.
- exact (a, (IHxs)).
Defined.

Definition bits2N {n} (bs: bits n) : option BinNums.N :=
  if Nat.eqb n 0
  then None
  else Some (Ascii.N_of_digits (bits2list bs)).

Definition bits2Z {n} (bs: bits n) : option BinNums.Z :=
  match bits2N bs with
  | None => None
  | Some n => Some (BinInt.Z.of_N n)
  end.

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

Definition reject {R} : PktParser R := state_fail tt.

Definition next_bit : PktParser bool :=
  let* st := get_state in
  match pkt st with
  | x :: pkt' =>
    put_state (fun st => st <| pkt := pkt' |>) ;;
    state_return x
  | _ => reject
  end.

Fixpoint extract_n (n: nat) : PktParser (bits n) :=
  match n with
  | 0 => state_return tt
  | S n' =>
    let* bit := next_bit in
    let* bits := extract_n n' in
    state_return (bit, bits)
  end.

Definition init_meta : StandardMeta := HAList.RCons zero_bits HAList.REmp.

Definition init_state (pkt: list bool) : ParserState :=
  {| fuel := 0; pkt := pkt; usr_meta := tt; std_meta := init_meta |}.

Definition lift_option {A : Type} (x: option A) : PktParser A :=
  Transformers.lift_opt tt x.
