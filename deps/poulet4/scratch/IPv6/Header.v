Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Grammars.Binary.
Require Import Grammars.Bits.
Require Import Vector.
Require Import Ascii.

Module IPV6Header.
  Record IPV6Header_t := {
    version : Nat.t ;
    traffic_class : bits 8 ;
    flow_label : bits 20 ;
    payload_len : Nat.t ;
    next_hdr : Nat.t ;
    hop_limit : Nat.t ;
    src_addr : bits 128 ;
    dst_addr : bits 128
  }.

  Definition version_p := filter (gbin_n 4) (Nat.eqb 6).
  Definition traffic_class_p := bits_n 8.
  Definition flow_label_p := bits_n 20.
  Definition payload_len_p := gbin_n 16.
  Definition next_hdr_p := gbin_n 8.
  Definition hop_limit_p := gbin_n 8.
  Definition addr_p := bits_n 128.

  Definition IPV6Header_p : grammar IPV6Header_t :=
    (version_p >= fun ver =>
    traffic_class_p >= fun tcp =>
    flow_label_p >= fun flp => 
    payload_len_p >= fun tail_len =>
    next_hdr_p >= fun nhp =>
    hop_limit_p >= fun hlp =>
    addr_p >= fun saddr =>
    addr_p >= fun daddr =>
    ret {| 
      version := ver ; 
      traffic_class := tcp ; 
      flow_label := flp ; 
      payload_len := tail_len ;
      next_hdr := nhp ; 
      hop_limit := hlp ; 
      src_addr := saddr ; 
      dst_addr := daddr 
    |}
    ) @ fun x => projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 x))))))).



    (* 
    an equivalent P4 program (modeled from ONOS fabric, https://github.com/opennetworkinglab/onos/blob/master/pipelines/fabric/impl/src/main/resources/fabric.p4) 
    
header ipv6_t {
    bit<4> version;
    bit<8> traffic_class;
    bit<20> flow_label;
    bit<16> payload_len;
    bit<8> next_hdr;
    bit<8> hop_limit;
    bit<128> src_addr;
    bit<128> dst_addr;
}

error { InvalidIPv6Header }

parser ipv6_parser(packet_in pkt, out ipv6_t hdr) {

  state start {
    pkt.extract(hdr);
    verify(hdr.version == 6, error.InvalidIPv6Header); 
    transition accept;
  }
}
    *)
End IPV6Header.