/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1876.p4
\n
#include<core.p4>
#include<v1model.p4>
struct H {}
struct M {}
parser P(packet_in pkt, out H h, inout M m, inout standard_metadata_t meta) { state start { transition accept; } }
control G(inout H h, inout M m, inout standard_metadata_t meta) { apply { } }
control C(inout H h, inout M m) { apply{ } }
control D(packet_out pkt, in H h) { apply { } }
V1Switch(P(), C(), G(), G(), C(), D()) main;
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
extern void hash<O, T8, D9, M10>(out O result, in HashAlgorithm algo,
                                 in T8 base, in D9 data, in M10 max);
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
parser Parser<H24, M25>
  (packet_in b,
   out H24 parsedHdr,
   inout M25 meta,
   inout standard_metadata_t standard_metadata);
control VerifyChecksum<H26, M27> (inout H26 hdr, inout M27 meta);
@pipeline
control Ingress<H28, M29>
  (inout H28 hdr, inout M29 meta, inout standard_metadata_t standard_metadata);
@pipeline
control Egress<H30, M31>
  (inout H30 hdr, inout M31 meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H32, M33> (inout H32 hdr, inout M33 meta);
@deparser
control Deparser<H34> (packet_out b, in H34 hdr);
package V1Switch<H35, M36>
  (Parser<H35, M36> p,
   VerifyChecksum<H35, M36> vr,
   Ingress<H35, M36> ig,
   Egress<H35, M36> eg,
   ComputeChecksum<H35, M36> ck,
   Deparser<H35> dep);
struct H {
  
}
struct M {
  
}
parser P(packet_in pkt, out H h, inout M m, inout standard_metadata_t meta) {
  state start {
    transition accept;
  }
}
control G(inout H h, inout M m, inout standard_metadata_t meta) {
  apply { 
  }
}
control C(inout H h, inout M m) {
  apply { 
  }
}
control D(packet_out pkt, in H h) {
  apply { 
  }
}
V1Switch(P(), C(), G(), G(), C(), D()) main;

************************\n******** p4c type checking result: ********\n************************\n
