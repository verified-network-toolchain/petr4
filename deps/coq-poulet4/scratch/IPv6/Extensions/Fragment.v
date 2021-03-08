Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Grammars.Binary.
Require Import Grammars.Bits.

Module Fragment.
  Record Fragment_t := {
    next_hdr : Nat.t ;
    reserved : bits 8 ;
    frag_offset : Nat.t ;
    res : bits 2 ;
    m_flag : bool ;
    identification: bits 32
  }.

  Definition next_hdr_p := gbin_n 8.
  Definition reserved_p := bits_n 8.
  Definition frag_offset_p := gbin_n 13.
  Definition res_p := bits_n 2.
  Definition m_flag_p := bit.
  Definition identification_p := bits_n 32.
  
  Definition Fragment_p : grammar Fragment_t :=
    (next_hdr_p >= fun next_hdr =>
    reserved_p >= fun reserved =>
    frag_offset_p >= fun frag_offset => 
    res_p >= fun res =>
    m_flag_p >= fun m =>
    identification_p >= fun ident =>
    ret {| 
      next_hdr := next_hdr ; 
      reserved := reserved ; 
      frag_offset := frag_offset ; 
      res := res ;
      m_flag := m ; 
      identification := ident 
    |}
    ) @ fun x => projT2 (projT2 (projT2 (projT2 (projT2 (projT2 x))))).

End Fragment.