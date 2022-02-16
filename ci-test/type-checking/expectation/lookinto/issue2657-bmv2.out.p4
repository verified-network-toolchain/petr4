/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2657-bmv2.p4
\n
#include <core.p4>
#define V1MODEL_VERSION 20200408
#include <v1model.p4>
header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

struct pkt_t {
    ethernet_t ethernet;
}

struct meta_t{

}

parser ParserImpl(packet_in packet, out pkt_t pkt, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract<ethernet_t>(pkt.ethernet);
        transition select(pkt.ethernet.etherType) {
            default: accept;
        }
    }

}



struct tuple_0 {
    bit<16> tmp1;
}

control egress(inout pkt_t pkt, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp;
    apply {
        hash<bit<16>, bit<9>, tuple_0, bit<18>>(tmp, HashAlgorithm.crc32, 9w0, { pkt.ethernet.etherType }, 18w512);
        pkt.ethernet.etherType = tmp;
    }
}

control ingress(inout pkt_t pkt, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in pkt_t pkt) {
    apply {
        packet.emit<ethernet_t>(pkt.ethernet);
    }
}

control verifyChecksum(inout pkt_t pkt, inout meta_t meta) {
    apply {
    }
}

control computeChecksum(inout pkt_t pkt, inout meta_t meta) {
    apply {
    }
}

V1Switch<pkt_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
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
const bit<32> __v1model_version = 20200408;
typedef bit<9> PortId_t;
@metadata
@name("standard_metadata")
struct standard_metadata_t {
  PortId_t ingress_port;
  PortId_t egress_spec;
  PortId_t egress_port;
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
extern counter<I> {
  counter(bit<32> size, CounterType type);
  void count(in I index);
}

extern direct_counter {
  direct_counter(CounterType type);
  void count();
}

extern meter<I3> {
  meter(bit<32> size, MeterType type);
  void execute_meter<T4>(in I3 index, out T4 result);
}

extern direct_meter<T5> {
  direct_meter(MeterType type);
  void read(out T5 result);
}

extern register<T6, I7> {
  register(bit<32> size);
  @noSideEffects
  void read(out T6 result, in I7 index);
  void write(in I7 index, in T6 value);
}

extern action_profile {
  action_profile(bit<32> size);
}

extern void random<T8>(out T8 result, in T8 lo, in T8 hi);
extern void digest<T9>(in bit<32> receiver, in T9 data);
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
extern void hash<O, T10, D, M>(out O result, in HashAlgorithm algo,
                               in T10 base, in D data, in M max);
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
  bit<16> get<D11>(in D11 data);
}

extern void verify_checksum<T12, O13>(in bool condition, in T12 data,
                                      in O13 checksum, HashAlgorithm algo);
@pure
extern void update_checksum<T14, O15>(in bool condition, in T14 data,
                                      inout O15 checksum,
                                      HashAlgorithm algo);
extern void verify_checksum_with_payload<T16, O17>(in bool condition,
                                                   in T16 data,
                                                   in O17 checksum,
                                                   HashAlgorithm algo);
@noSideEffects
extern void update_checksum_with_payload<T18, O19>(in bool condition,
                                                   in T18 data,
                                                   inout O19 checksum,
                                                   HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead")
extern void resubmit<T20>(in T20 data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead")
extern void recirculate<T21>(in T21 data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead")
extern void clone3<T22>(in CloneType type, in bit<32> session, in T22 data);
extern void clone_preserving_field_list(in CloneType type,
                                        in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T23>(string msg, in T23 data);
parser Parser<H, M24>
  (packet_in b,
   out H parsedHdr,
   inout M24 meta,
   inout standard_metadata_t standard_metadata);
control VerifyChecksum<H25, M26> (inout H25 hdr, inout M26 meta);
@pipeline
control Ingress<H27, M28>
  (inout H27 hdr, inout M28 meta, inout standard_metadata_t standard_metadata);
@pipeline
control Egress<H29, M30>
  (inout H29 hdr, inout M30 meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H31, M32> (inout H31 hdr, inout M32 meta);
@deparser
control Deparser<H33> (packet_out b, in H33 hdr);
package V1Switch<H34, M35>
  (Parser<H34, M35> p,
   VerifyChecksum<H34, M35> vr,
   Ingress<H34, M35> ig,
   Egress<H34, M35> eg,
   ComputeChecksum<H34, M35> ck,
   Deparser<H34> dep);
header ethernet_t {
  bit<48> dstAddr;
  bit<48> srcAddr;
  bit<16> etherType;
}
struct pkt_t {
  ethernet_t ethernet;
}
struct meta_t {
  
}
parser ParserImpl(packet_in packet, out pkt_t pkt, inout meta_t meta,
                  inout standard_metadata_t standard_metadata) {
  state start
    {
    packet.extract<ethernet_t>(pkt.ethernet);
    transition select(pkt.ethernet.etherType) {
      default: accept;
    }
  }
}
struct tuple_0 {
  bit<16> tmp1;
}
control egress(inout pkt_t pkt, inout meta_t meta,
               inout standard_metadata_t standard_metadata) {
  bit<16> tmp;
  apply
    {
    hash<bit<16>,
    bit<9>,
    tuple_0,
    bit<18>>(tmp, HashAlgorithm.crc32, 9w0, {pkt.ethernet.etherType}, 18w512);
    pkt.ethernet.etherType = tmp;
  }
}
control ingress(inout pkt_t pkt, inout meta_t meta,
                inout standard_metadata_t standard_metadata) {
  apply { 
  }
}
control DeparserImpl(packet_out packet, in pkt_t pkt) {
  apply {
    packet.emit<ethernet_t>(pkt.ethernet);
  }
}
control verifyChecksum(inout pkt_t pkt, inout meta_t meta) {
  apply { 
  }
}
control computeChecksum(inout pkt_t pkt, inout meta_t meta) {
  apply { 
  }
}
V1Switch<pkt_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(),
                          computeChecksum(), DeparserImpl())
  main;

************************\n******** p4c type checking result: ********\n************************\n
