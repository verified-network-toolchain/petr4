/petr4/ci-test/type-checking/testdata/p4_16_samples/issue983-bmv2.p4
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

#include <core.p4>
#include <v1model.p4>


typedef bit<48>  EthernetAddress;

header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct fwd_meta_t {
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    bit<32> x3;
    bit<32> x4;
    bit<16> exp_etherType;
    bit<32> exp_x1;
    bit<16> exp_x2;
    bit<32> exp_x3;
    bit<32> exp_x4;
}

struct metadata {
    fwd_meta_t fwd_meta;
}

struct headers {
    ethernet_t       ethernet;
}


parser IngressParserImpl(packet_in buffer,
                         out headers hdr,
                         inout metadata user_meta,
                         inout standard_metadata_t standard_metadata)
{
    state start {
        buffer.extract(hdr.ethernet);
        transition accept;
    }
}

control ingress(inout headers hdr,
                inout metadata user_meta,
                inout standard_metadata_t standard_metadata) {
    table debug_table_cksum1 {
        key = {
            hdr.ethernet.srcAddr : exact;
            hdr.ethernet.dstAddr : exact;
            hdr.ethernet.etherType : exact;
            user_meta.fwd_meta.exp_etherType : exact;
            user_meta.fwd_meta.tmp : exact;
            user_meta.fwd_meta.exp_x1 : exact;
            user_meta.fwd_meta.x1 : exact;
            user_meta.fwd_meta.exp_x2 : exact;
            user_meta.fwd_meta.x2 : exact;
            user_meta.fwd_meta.exp_x3 : exact;
            user_meta.fwd_meta.x3 : exact;
            user_meta.fwd_meta.exp_x4 : exact;
            user_meta.fwd_meta.x4 : exact;
        }
        actions = { NoAction; }
    }
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    apply {
        tmp = ~hdr.ethernet.etherType;

        x1 = (bit<32>) tmp;
        x2 = x1[31:16] + x1[15:0];

        user_meta.fwd_meta.tmp = tmp;
        user_meta.fwd_meta.x1 = x1;
        user_meta.fwd_meta.x2 = x2;
        user_meta.fwd_meta.x3 = (bit<32>) ~hdr.ethernet.etherType;
        user_meta.fwd_meta.x4 = ~((bit<32>) hdr.ethernet.etherType);

        user_meta.fwd_meta.exp_etherType = 0x0800;
        user_meta.fwd_meta.exp_x1 = (bit<32>) (~16w0x0800);
        user_meta.fwd_meta.exp_x2 = (~16w0x0800);
        user_meta.fwd_meta.exp_x3 = (bit<32>) (~16w0x0800);
        user_meta.fwd_meta.exp_x4 = (~32w0x0800);

        // Use dstAddr field of Ethernet header to store 'error
        // codes', so they are easily checkable in output packet.
        hdr.ethernet.dstAddr = 0;
        if (hdr.ethernet.etherType != user_meta.fwd_meta.exp_etherType) {
            hdr.ethernet.dstAddr[47:40] = 1;
        }
        if (user_meta.fwd_meta.x1 != user_meta.fwd_meta.exp_x1) {
            hdr.ethernet.dstAddr[39:32] = 1;
        }
        if (user_meta.fwd_meta.x2 != user_meta.fwd_meta.exp_x2) {
            hdr.ethernet.dstAddr[31:24] = 1;
        }
        if (user_meta.fwd_meta.x3 != user_meta.fwd_meta.exp_x3) {
            hdr.ethernet.dstAddr[23:16] = 1;
        }
        if (user_meta.fwd_meta.x4 != user_meta.fwd_meta.exp_x4) {
            hdr.ethernet.dstAddr[15:8] = 1;
        }
        debug_table_cksum1.apply();
    }
}

control egress(inout headers hdr,
               inout metadata user_meta,
               inout standard_metadata_t standard_metadata)
{
    apply { }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

V1Switch(IngressParserImpl(),
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
struct fwd_meta_t {
  bit<16> tmp;
  bit<32> x1;
  bit<16> x2;
  bit<32> x3;
  bit<32> x4;
  bit<16> exp_etherType;
  bit<32> exp_x1;
  bit<16> exp_x2;
  bit<32> exp_x3;
  bit<32> exp_x4;
}
struct metadata {
  fwd_meta_t fwd_meta;
}
struct headers {
  ethernet_t ethernet;
}
parser IngressParserImpl(packet_in buffer, out headers hdr,
                         inout metadata user_meta,
                         inout standard_metadata_t standard_metadata) {
  state start {
    buffer.extract(hdr.ethernet);
    transition accept;
  }
}
control ingress(inout headers hdr, inout metadata user_meta,
                inout standard_metadata_t standard_metadata) {
  table debug_table_cksum1
    {
    key =
      {
      hdr.ethernet.srcAddr: exact;
      hdr.ethernet.dstAddr: exact;
      hdr.ethernet.etherType: exact;
      user_meta.fwd_meta.exp_etherType: exact;
      user_meta.fwd_meta.tmp: exact;
      user_meta.fwd_meta.exp_x1: exact;
      user_meta.fwd_meta.x1: exact;
      user_meta.fwd_meta.exp_x2: exact;
      user_meta.fwd_meta.x2: exact;
      user_meta.fwd_meta.exp_x3: exact;
      user_meta.fwd_meta.x3: exact;
      user_meta.fwd_meta.exp_x4: exact;
      user_meta.fwd_meta.x4: exact;
    }
    actions = {
      NoAction;
    }
  }
  bit<16> tmp;
  bit<32> x1;
  bit<16> x2;
  apply
    {
    tmp = ~hdr.ethernet.etherType;
    x1 = (bit<32>) tmp;
    x2 = x1[31:16]+x1[15:0];
    user_meta.fwd_meta.tmp = tmp;
    user_meta.fwd_meta.x1 = x1;
    user_meta.fwd_meta.x2 = x2;
    user_meta.fwd_meta.x3 = (bit<32>) ~hdr.ethernet.etherType;
    user_meta.fwd_meta.x4 = ~(bit<32>) hdr.ethernet.etherType;
    user_meta.fwd_meta.exp_etherType = 2048;
    user_meta.fwd_meta.exp_x1 = (bit<32>) ~16w2048;
    user_meta.fwd_meta.exp_x2 = ~16w2048;
    user_meta.fwd_meta.exp_x3 = (bit<32>) ~16w2048;
    user_meta.fwd_meta.exp_x4 = ~32w2048;
    hdr.ethernet.dstAddr = 0;
    if (hdr.ethernet.etherType!=user_meta.fwd_meta.exp_etherType)
      {
      hdr.ethernet.dstAddr[47:40] = 1;
    }
    if (user_meta.fwd_meta.x1!=user_meta.fwd_meta.exp_x1)
      {
      hdr.ethernet.dstAddr[39:32] = 1;
    }
    if (user_meta.fwd_meta.x2!=user_meta.fwd_meta.exp_x2)
      {
      hdr.ethernet.dstAddr[31:24] = 1;
    }
    if (user_meta.fwd_meta.x3!=user_meta.fwd_meta.exp_x3)
      {
      hdr.ethernet.dstAddr[23:16] = 1;
    }
    if (user_meta.fwd_meta.x4!=user_meta.fwd_meta.exp_x4)
      {
      hdr.ethernet.dstAddr[15:8] = 1;
    }
    debug_table_cksum1.apply();
  }
}
control egress(inout headers hdr, inout metadata user_meta,
               inout standard_metadata_t standard_metadata) {
  apply { 
  }
}
control DeparserImpl(packet_out packet, in headers hdr) {
  apply {
    packet.emit(hdr.ethernet);
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
V1Switch(IngressParserImpl(), verifyChecksum(), ingress(), egress(),
           computeChecksum(), DeparserImpl())
  main;

************************\n******** p4c type checking result: ********\n************************\n
