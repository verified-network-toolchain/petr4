
Require Import Coq.Lists.List.

Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Grammars.Binary.
Require Import Grammars.Bits.
Require Import Vector.
Require Import Ascii.


Require Import BinNat.

Import ListNotations.
Import VectorNotations.

Open Scope list_scope.


(* 
// a parser for hop-by-hop options
header pad0 {
}

header padn {
  varbit<8*24> data;
}

header jumbo {
  bit<32> payload_length;
}

header_union hop_value {
  padn t0;
  jumbo t1;
}


header hop_opt_len_value {
  bit<8> len;
  hop_value value;
}

header_union hop_opt_payload {
  pad0 special;
  hop_opt_len_value general;
}

header hop_opt {
  bit<8> type;
  hop_opt_payload payload;
}

header hbh_opts {
  bit<8> nxt_hdr_t;
  bit<8> total_len;
  hop_opt[8*24] opts;
}

parser hbh_parser(packet_in pkt, out hbh_opts hdr) {

  int idx = 0;

  state start {
    pkt.extract(hdr.nxt_hdr_t);
    pkt.extract(hdr.total_len);

    transition select(hdr.total_len) {
      0: reject;
      1: reject;
      default: parse_opt;
    }
  }

  state parse_opt {
    pkt.extract(hdr.opts[idx].type);

    transition select(hdr.opts[idx].type) {
      0 : parse_pad0;
      1 : parse_padn;
      default : reject;
    }
  }

  state parse_pad0 {
    pkt.extract(hdr.opts[idx].value.t1);
    
    transition loop;
  }

  state parse_padn {
    pkt.extract(hdr.opts[idx].value.t2.len);
    pkt.extract(hdr.opts[idx].value.t2.data, hdr.opts[idx].value.t2.len);

    transition loop;
  }

  state loop {
    idx = idx + 1;
    transition select(idx + 2 == hdr.total_len) {
      true  : accept;
      false : parse_opt; 
    }
  }
}

*)

(* hand translation: *)

Definition pad0_t : grammar unit := gone.
Definition padn_t (len: nat) := repeat len (bits_n 8).

Definition parse_padn : grammar {len: nat & Vector.t (bits 8) len} := gbin_n 8 >= padn_t.
Definition parse_pad0 : grammar unit := gone.

Definition b2c (b: bool) : ascii := if b then "1" else "0".

Definition parse_opt : grammar (unit + {x : nat & Vector.t (bits 8) x} ) := 
  (
    gbin_n 8 >= fun type_tag => 
    if Nat.eqb type_tag 0 then parse_pad0 @ inl else 
    if Nat.eqb type_tag 1 then parse_padn @ inr else
    gzero
  ) @ fun x => projT2 x.

(* Here is a declarative version of the loop
    repeat is a combinator: (len: nat) -> grammar A -> grammar (Vector.t A len)
*)
Definition loop (total_len: nat) := repeat (total_len - 2) parse_opt.

(*  Here is a stateful version that faithfully tracks the idx variable. 
    It's rather unpleasant...
*)
Definition payload_t : Set := (unit + {x : nat & Vector.t (bits 8) x}).

Definition loop_stateful_step : grammar (nat -> nat * payload_t) := 
  ((ret (fun y => y + 1)) $ parse_opt) @ fun '(eff, p) => fun x => (eff x, p).

Definition update_step (acc: nat -> nat * list payload_t) (eff : nat -> nat * payload_t) : (nat -> nat * list payload_t) :=
  fun init => 
    let '(counter, payloads) := acc init in 
    let '(counter', payload) := eff counter in 
    (counter', payloads ++ [payload]).

Definition loop_stateful_star: grammar (nat -> nat * list payload_t) := 
  gstar loop_stateful_step @ (
    fun xs => 
      List.fold_left update_step xs (fun init => (init, []))
  ).

Definition loop_stateful_len (len: nat) (init: nat) : grammar (list payload_t) :=
  (filter loop_stateful_star (fun eff => Nat.eqb (fst (eff init) + 2) len))
  @ fun eff => snd (eff init).

(* Extensible version with jumbo options *)
Definition jumbo_t := filter (gbin_n 32) (Nat.leb 65535).

Definition hop_opt_builder {F: nat -> nat -> Set} (opt_parser: forall typ len, grammar (F typ len)) : grammar {type : nat & (unit + {len: nat & (Vector.t (bits 8) len) + (F type len)})%type} :=
  gbin_n 8 >= fun type => 
  if Nat.eqb type 0 then 
    pad0_t @ inl else
  (
    gbin_n 8 >= fun len =>  
    if Nat.eqb type 1 then 
    padn_t len @ inl else
    opt_parser type len @ inr
  ) @ inr.

Definition hbh_opts := hop_opt_builder (fun _ _ => jumbo_t).