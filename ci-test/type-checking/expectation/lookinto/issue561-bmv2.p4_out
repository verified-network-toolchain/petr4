/petr4/ci-test/type-checking/testdata/p4_16_samples/issue561-bmv2.p4
\n
/*
Copyright 2017 Cisco Systems, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

/*
The TCP option parsing part of this program has been adapted from
testdata/p4_16_samples/spec-ex19.p4 within the repository
https://github.com/p4lang/p4c by Andy Fingerhut
(andy.fingerhut@gmail.com).  That earlier version also appears in
the P4_16 v1.0.0 specification document.

As of 2017-Nov-09, the P4_16 compiler `p4test` in
https://github.com/p4lang/p4c compiles tcp-options-parser.p4 without
any errors, but `p4c-bm2-ss` gives an error that Tcp_option_h is not a
header type.  This is because as of that date the bmv2 back end code
in `p4c-bm2-ss` code does not yet handle header_union.
*/

#include <core.p4>
#include <v1model.p4>

typedef bit<48>  EthernetAddress;

header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

header tcp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

header Tcp_option_end_h {
    bit<8> kind;
}
header Tcp_option_nop_h {
    bit<8> kind;
}
header Tcp_option_ss_h {
    bit<8>  kind;
    bit<32> maxSegmentSize;
}
header Tcp_option_s_h {
    bit<8>  kind;
    bit<24> scale;
}
header Tcp_option_sack_h {
    bit<8>         kind;
    bit<8>         length;
    varbit<256>    sack;
}
header_union Tcp_option_h {
    Tcp_option_end_h  end;
    Tcp_option_nop_h  nop;
    Tcp_option_ss_h   ss;
    Tcp_option_s_h    s;
    Tcp_option_sack_h sack;
}

// Defines a stack of 10 tcp options
typedef Tcp_option_h[10] Tcp_option_stack;

header Tcp_option_padding_h {
    varbit<256> padding;
}

struct headers {
    ethernet_t       ethernet;
    ipv4_t           ipv4;
    tcp_t            tcp;
    Tcp_option_stack tcp_options_vec;
    Tcp_option_padding_h tcp_options_padding;
}

struct fwd_metadata_t {
    bit<32> l2ptr;
    bit<24> out_bd;
}

struct metadata {
    fwd_metadata_t fwd_metadata;
}

error {
    TcpDataOffsetTooSmall,
    TcpOptionTooLongForHeader,
    TcpBadSackOptionLength
}

struct Tcp_option_sack_top
{
    bit<8> kind;
    bit<8> length;
}

// This sub-parser is intended to be apply'd just after the base
// 20-byte TCP header has been extracted.  It should be called with
// the value of the Data Offset field.  It will fill in the @vec
// argument with a stack of TCP options found, perhaps empty.

// Unless some error is detect earlier (causing this sub-parser to
// transition to the reject state), it will advance exactly to the end
// of the TCP header, leaving the packet 'pointer' at the first byte
// of the TCP payload (if any).  If the packet ends before the full
// TCP header can be consumed, this sub-parser will set
// error.PacketTooShort and transition to reject.

parser Tcp_option_parser(packet_in b,
                         in bit<4> tcp_hdr_data_offset,
                         out Tcp_option_stack vec,
                         out Tcp_option_padding_h padding)
{
    bit<7> tcp_hdr_bytes_left;

    state start {
        // RFC 793 - the Data Offset field is the length of the TCP
        // header in units of 32-bit words.  It must be at least 5 for
        // the minimum length TCP header, and since it is 4 bits in
        // size, can be at most 15, for a maximum TCP header length of
        // 15*4 = 60 bytes.
        verify(tcp_hdr_data_offset >= 5, error.TcpDataOffsetTooSmall);
        tcp_hdr_bytes_left = 4 * (bit<7>) (tcp_hdr_data_offset - 5);
        // always true here: 0 <= tcp_hdr_bytes_left <= 40
        transition next_option;
    }
    state next_option {
        transition select(tcp_hdr_bytes_left) {
            0 : accept;  // no TCP header bytes left
            default : next_option_part2;
        }
    }
    state next_option_part2 {
        // precondition: tcp_hdr_bytes_left >= 1
        transition select(b.lookahead<bit<8>>()) {
            0: parse_tcp_option_end;
            1: parse_tcp_option_nop;
            2: parse_tcp_option_ss;
            3: parse_tcp_option_s;
            5: parse_tcp_option_sack;
        }
    }
    state parse_tcp_option_end {
        b.extract(vec.next.end);
        // TBD: This code is an example demonstrating why it would be
        // useful to have sizeof(vec.next.end) instead of having to
        // put in a hard-coded length for each TCP option.
        tcp_hdr_bytes_left = tcp_hdr_bytes_left - 1;
        transition consume_remaining_tcp_hdr_and_accept;
    }
    state consume_remaining_tcp_hdr_and_accept {
        // A more picky sub-parser implementation would verify that
        // all of the remaining bytes are 0, as specified in RFC 793,
        // setting an error and rejecting if not.  This one skips past
        // the rest of the TCP header without checking this.

        // tcp_hdr_bytes_left might be as large as 40, so multiplying
        // it by 8 it may be up to 320, which requires 9 bits to avoid
        // losing any information.
        b.extract(padding, (bit<32>) (8 * (bit<9>) tcp_hdr_bytes_left));
        transition accept;
    }
    state parse_tcp_option_nop {
        b.extract(vec.next.nop);
        tcp_hdr_bytes_left = tcp_hdr_bytes_left - 1;
        transition next_option;
    }
    state parse_tcp_option_ss {
        verify(tcp_hdr_bytes_left >= 5, error.TcpOptionTooLongForHeader);
        tcp_hdr_bytes_left = tcp_hdr_bytes_left - 5;
        b.extract(vec.next.ss);
        transition next_option;
    }
    state parse_tcp_option_s {
        verify(tcp_hdr_bytes_left >= 4, error.TcpOptionTooLongForHeader);
        tcp_hdr_bytes_left = tcp_hdr_bytes_left - 4;
        b.extract(vec.next.s);
        transition next_option;
    }
    state parse_tcp_option_sack {
        bit<8> n_sack_bytes = b.lookahead<Tcp_option_sack_top>().length;
        // I do not have global knowledge of all TCP SACK
        // implementations, but from reading the RFC, it appears that
        // the only SACK option lengths that are legal are 2+8*n for
        // n=1, 2, 3, or 4, so set an error if anything else is seen.
        verify(n_sack_bytes == 10 || n_sack_bytes == 18 ||
               n_sack_bytes == 26 || n_sack_bytes == 34,
               error.TcpBadSackOptionLength);
        verify(tcp_hdr_bytes_left >= (bit<7>) n_sack_bytes,
               error.TcpOptionTooLongForHeader);
        tcp_hdr_bytes_left = tcp_hdr_bytes_left - (bit<7>) n_sack_bytes;
        b.extract(vec.next.sack, (bit<32>) (8 * n_sack_bytes - 16));
        transition next_option;
    }
}

parser ParserImpl(packet_in packet,
                  out headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata)
{
    const bit<16> ETHERTYPE_IPV4 = 0x0800;

    state start {
        transition parse_ethernet;
    }
    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            ETHERTYPE_IPV4: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            6: parse_tcp;
            default: accept;
        }
    }
    state parse_tcp {
        packet.extract(hdr.tcp);
        Tcp_option_parser.apply(packet, hdr.tcp.dataOffset,
                                hdr.tcp_options_vec, hdr.tcp_options_padding);
        transition accept;
    }
}

action my_drop(inout standard_metadata_t smeta) {
    mark_to_drop(smeta);
}

control ingress(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    action set_l2ptr(bit<32> l2ptr) {
        meta.fwd_metadata.l2ptr = l2ptr;
    }
    table ipv4_da_lpm {
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        actions = {
            set_l2ptr;
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }

    action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
        meta.fwd_metadata.out_bd = bd;
        hdr.ethernet.dstAddr = dmac;
        standard_metadata.egress_spec = intf;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
    }
    table mac_da {
        key = {
            meta.fwd_metadata.l2ptr: exact;
        }
        actions = {
            set_bd_dmac_intf;
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }

    apply {
        ipv4_da_lpm.apply();
        mac_da.apply();
    }
}

control egress(inout headers hdr,
               inout metadata meta,
               inout standard_metadata_t standard_metadata)
{
    action rewrite_mac(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
    }
    table send_frame {
        key = {
            meta.fwd_metadata.out_bd: exact;
        }
        actions = {
            rewrite_mac;
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }

    apply {
        send_frame.apply();
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.tcp);
        packet.emit(hdr.tcp_options_vec);
        packet.emit(hdr.tcp_options_padding);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch(ParserImpl(),
         verifyChecksum(),
         ingress(),
         egress(),
         computeChecksum(),
         DeparserImpl()) main;
************************\n******** petr4 type checking result: ********\n************************\n
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}
match_kind {
  range, optional, selector
}
const bit<32> __v1model_version = 20180101;
@metadata
@name("standard_metadata")
struct standard_metadata_t {
  bit<9> ingress_port;
  bit<9> egress_spec;
  bit<9> egress_port;
  bit<32> instance_type;
  bit<32> packet_length;
  @alias("queueing_metadata.enq_timestamp")
  bit<32> enq_timestamp;
  @alias("queueing_metadata.enq_qdepth")
  bit<19> enq_qdepth;
  @alias("queueing_metadata.deq_timedelta")
  bit<32> deq_timedelta;
  @alias("queueing_metadata.deq_qdepth")
  bit<19>
  deq_qdepth;
  @alias("intrinsic_metadata.ingress_global_timestamp")
  bit<48>
  ingress_global_timestamp;
  @alias("intrinsic_metadata.egress_global_timestamp")
  bit<48>
  egress_global_timestamp;
  @alias("intrinsic_metadata.mcast_grp")
  bit<16> mcast_grp;
  @alias("intrinsic_metadata.egress_rid")
  bit<16> egress_rid;
  bit<1> checksum_error;
  error parser_error;
  @alias("intrinsic_metadata.priority")
  bit<3> priority;
}
enum CounterType {
  packets, 
  bytes, 
  packets_and_bytes
}
enum MeterType {
  packets, 
  bytes
}
extern counter {
  counter(bit<32> size, CounterType type);
  void count(in bit<32> index);
}

extern direct_counter {
  direct_counter(CounterType type);
  void count();
}

extern meter {
  meter(bit<32> size, MeterType type);
  void execute_meter<T3>(in bit<32> index, out T3 result);
}

extern direct_meter<T4> {
  direct_meter(MeterType type);
  void read(out T4 result);
}

extern register<T5> {
  register(bit<32> size);
  @noSideEffects
  void read(out T5 result, in bit<32> index);
  void write(in bit<32> index, in T5 value);
}

extern action_profile {
  action_profile(bit<32> size);
}

extern void random<T6>(out T6 result, in T6 lo, in T6 hi);
extern void digest<T7>(in bit<32> receiver, in T7 data);
enum HashAlgorithm {
  crc32, 
  crc32_custom, 
  crc16, 
  crc16_custom, 
  random, 
  identity, 
  csum16, 
  xor16
}
@deprecated("Please use mark_to_drop(standard_metadata) instead.")
extern void mark_to_drop();
@pure
extern void mark_to_drop(inout standard_metadata_t standard_metadata);
@pure
extern void hash<O, T8, D, M>(out O result, in HashAlgorithm algo,
                              in T8 base, in D data, in M max);
extern action_selector {
  action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

enum CloneType {
  I2E, 
  E2E
}
@deprecated("Please use verify_checksum/update_checksum instead.")
extern Checksum16 {
  Checksum16();
  bit<16> get<D9>(in D9 data);
}

extern void verify_checksum<T10, O11>(in bool condition, in T10 data,
                                      in O11 checksum, HashAlgorithm algo);
@pure
extern void update_checksum<T12, O13>(in bool condition, in T12 data,
                                      inout O13 checksum,
                                      HashAlgorithm algo);
extern void verify_checksum_with_payload<T14, O15>(in bool condition,
                                                   in T14 data,
                                                   in O15 checksum,
                                                   HashAlgorithm algo);
@noSideEffects
extern void update_checksum_with_payload<T16, O17>(in bool condition,
                                                   in T16 data,
                                                   inout O17 checksum,
                                                   HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead")
extern void resubmit<T18>(in T18 data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead")
extern void recirculate<T19>(in T19 data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead")
extern void clone3<T20>(in CloneType type, in bit<32> session, in T20 data);
extern void clone_preserving_field_list(in CloneType type,
                                        in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T21>(string msg, in T21 data);
parser Parser<H, M22>
  (packet_in b,
   out H parsedHdr,
   inout M22 meta,
   inout standard_metadata_t standard_metadata);
control VerifyChecksum<H23, M24> (inout H23 hdr, inout M24 meta);
@pipeline
control Ingress<H25, M26>
  (inout H25 hdr, inout M26 meta, inout standard_metadata_t standard_metadata);
@pipeline
control Egress<H27, M28>
  (inout H27 hdr, inout M28 meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H29, M30> (inout H29 hdr, inout M30 meta);
@deparser
control Deparser<H31> (packet_out b, in H31 hdr);
package V1Switch<H32, M33>
  (Parser<H32, M33> p,
   VerifyChecksum<H32, M33> vr,
   Ingress<H32, M33> ig,
   Egress<H32, M33> eg,
   ComputeChecksum<H32, M33> ck,
   Deparser<H32> dep);
typedef bit<48> EthernetAddress;
header ethernet_t {
  EthernetAddress dstAddr;
  EthernetAddress srcAddr;
  bit<16> etherType;
}
header ipv4_t {
  bit<4> version;
  bit<4> ihl;
  bit<8> diffserv;
  bit<16> totalLen;
  bit<16> identification;
  bit<3> flags;
  bit<13> fragOffset;
  bit<8> ttl;
  bit<8> protocol;
  bit<16> hdrChecksum;
  bit<32> srcAddr;
  bit<32> dstAddr;
}
header tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
  bit<32> seqNo;
  bit<32> ackNo;
  bit<4> dataOffset;
  bit<3> res;
  bit<3> ecn;
  bit<6> ctrl;
  bit<16> window;
  bit<16> checksum;
  bit<16> urgentPtr;
}
header Tcp_option_end_h {
  bit<8> kind;
}
header Tcp_option_nop_h {
  bit<8> kind;
}
header Tcp_option_ss_h {
  bit<8> kind;
  bit<32> maxSegmentSize;
}
header Tcp_option_s_h {
  bit<8> kind;
  bit<24> scale;
}
header Tcp_option_sack_h {
  bit<8> kind;
  bit<8> length;
  varbit <256> sack;
}
header_union Tcp_option_h {
  Tcp_option_end_h end;
  Tcp_option_nop_h nop;
  Tcp_option_ss_h ss;
  Tcp_option_s_h s;
  Tcp_option_sack_h sack;
}
typedef Tcp_option_h[10] Tcp_option_stack;
header Tcp_option_padding_h {
  varbit <256> padding;
}
struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
  tcp_t tcp;
  Tcp_option_stack tcp_options_vec;
  Tcp_option_padding_h tcp_options_padding;
}
struct fwd_metadata_t {
  bit<32> l2ptr;
  bit<24> out_bd;
}
struct metadata {
  fwd_metadata_t fwd_metadata;
}
error {
  TcpDataOffsetTooSmall, TcpOptionTooLongForHeader, TcpBadSackOptionLength
}
struct Tcp_option_sack_top {
  bit<8> kind;
  bit<8> length;
}
parser Tcp_option_parser(packet_in b, in bit<4> tcp_hdr_data_offset,
                         out Tcp_option_stack vec,
                         out Tcp_option_padding_h padding) {
  bit<7> tcp_hdr_bytes_left;
  state start
    {
    verify(tcp_hdr_data_offset>=5, TcpDataOffsetTooSmall);
    tcp_hdr_bytes_left = 4*(bit<7>) tcp_hdr_data_offset-5;
    transition next_option;
  }
  state next_option
    {
    transition select(tcp_hdr_bytes_left) {
      0: accept;
      default: next_option_part2;
    }
  }
  state next_option_part2
    {
    transition select(b.lookahead<bit<8>>()) {
      0: parse_tcp_option_end;
      1: parse_tcp_option_nop;
      2: parse_tcp_option_ss;
      3: parse_tcp_option_s;
      5: parse_tcp_option_sack;
    }
  }
  state parse_tcp_option_end
    {
    b.extract(vec.next.end);
    tcp_hdr_bytes_left = tcp_hdr_bytes_left-1;
    transition consume_remaining_tcp_hdr_and_accept;
  }
  state consume_remaining_tcp_hdr_and_accept
    {
    b.extract(padding, (bit<32>) 8*(bit<9>) tcp_hdr_bytes_left);
    transition accept;
  }
  state parse_tcp_option_nop
    {
    b.extract(vec.next.nop);
    tcp_hdr_bytes_left = tcp_hdr_bytes_left-1;
    transition next_option;
  }
  state parse_tcp_option_ss
    {
    verify(tcp_hdr_bytes_left>=5, TcpOptionTooLongForHeader);
    tcp_hdr_bytes_left = tcp_hdr_bytes_left-5;
    b.extract(vec.next.ss);
    transition next_option;
  }
  state parse_tcp_option_s
    {
    verify(tcp_hdr_bytes_left>=4, TcpOptionTooLongForHeader);
    tcp_hdr_bytes_left = tcp_hdr_bytes_left-4;
    b.extract(vec.next.s);
    transition next_option;
  }
  state parse_tcp_option_sack
    {
    bit<8> n_sack_bytes = b.lookahead<Tcp_option_sack_top>().length;
    verify(n_sack_bytes==10 || n_sack_bytes==18 || n_sack_bytes==26 || n_sack_bytes==34,
             TcpBadSackOptionLength);
    verify(tcp_hdr_bytes_left>=(bit<7>) n_sack_bytes,
             TcpOptionTooLongForHeader);
    tcp_hdr_bytes_left = tcp_hdr_bytes_left-(bit<7>) n_sack_bytes;
    b.extract(vec.next.sack, (bit<32>) 8*n_sack_bytes-16);
    transition next_option;
  }
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  const bit<16> ETHERTYPE_IPV4 = 2048;
  state start {
    transition parse_ethernet;
  }
  state parse_ethernet
    {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType) {
      ETHERTYPE_IPV4: parse_ipv4;
      default: accept;
    }
  }
  state parse_ipv4
    {
    packet.extract(hdr.ipv4);
    transition select(hdr.ipv4.protocol) {
      6: parse_tcp;
      default: accept;
    }
  }
  state parse_tcp
    {
    packet.extract(hdr.tcp);
    Tcp_option_parser.apply(packet, hdr.tcp.dataOffset, hdr.tcp_options_vec,
                              hdr.tcp_options_padding);
    transition accept;
  }
}
action my_drop(inout standard_metadata_t smeta) {
  mark_to_drop(smeta);
}
control ingress(inout headers hdr, inout metadata meta,
                inout standard_metadata_t standard_metadata) {
  action set_l2ptr(bit<32> l2ptr) {
    meta.fwd_metadata.l2ptr = l2ptr;
  }
  table ipv4_da_lpm
    {
    key = {
      hdr.ipv4.dstAddr: lpm;
    }
    actions = {
      set_l2ptr;my_drop(standard_metadata);
    }
    default_action = my_drop(standard_metadata);
  }
  action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf)
    {
    meta.fwd_metadata.out_bd = bd;
    hdr.ethernet.dstAddr = dmac;
    standard_metadata.egress_spec = intf;
    hdr.ipv4.ttl = hdr.ipv4.ttl-1;
  }
  table mac_da
    {
    key = {
      meta.fwd_metadata.l2ptr: exact;
    }
    actions = {
      set_bd_dmac_intf;my_drop(standard_metadata);
    }
    default_action = my_drop(standard_metadata);
  }
  apply {
    ipv4_da_lpm.apply();
    mac_da.apply();
  }
}
control egress(inout headers hdr, inout metadata meta,
               inout standard_metadata_t standard_metadata) {
  action rewrite_mac(bit<48> smac) {
    hdr.ethernet.srcAddr = smac;
  }
  table send_frame
    {
    key = {
      meta.fwd_metadata.out_bd: exact;
    }
    actions = {
      rewrite_mac;my_drop(standard_metadata);
    }
    default_action = my_drop(standard_metadata);
  }
  apply {
    send_frame.apply();
  }
}
control DeparserImpl(packet_out packet, in headers hdr) {
  apply
    {
    packet.emit(hdr.ethernet);
    packet.emit(hdr.ipv4);
    packet.emit(hdr.tcp);
    packet.emit(hdr.tcp_options_vec);
    packet.emit(hdr.tcp_options_padding);
  }
}
control verifyChecksum(inout headers hdr, inout metadata meta) {
  apply { 
  }
}
control computeChecksum(inout headers hdr, inout metadata meta) {
  apply { 
  }
}
V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(),
           computeChecksum(), DeparserImpl())
  main;

************************\n******** p4c type checking result: ********\n************************\n
