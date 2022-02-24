/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4
\n
#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header OVERFLOW {
    bit<8> a;
    bit<8> b;
}

header UNDERFLOW {
    bit<8> a;
    bit<8> b;
    bit<8> c;
}

header MOD {
    bit<4> a;
    bit<4> b;
    bit<4> c;
    bit<4> d;
}

header RSH {
    bit<4> a;
    int<4>  b;
    bit<4>  c;
    int<4>  d;
    bit<4>  e;
    bit<4>  g;
    bit<8>  h;
}

header LSH {
    bit<8> a;
    bit<8> b;
    bit<8> c;
    bit<8> d;
    bit<8> e;
}

header COMPARE {
    bit<8> a;
    bit<8> b;
    bit<8> c;
    bit<8> d;
    bit<8> e;
}

header DIV {
    bit<8> a;
    bit<8> b;
    bit<8> c;
}

header BOOL {
    bool a;
    bit<7> padding;
}

struct Headers {
    ethernet_t eth_hdr;
    OVERFLOW overflow;
    UNDERFLOW underflow;
    RSH rshift;
    LSH lshift;
    MOD mod;
    COMPARE comp;
    DIV div;
    BOOL b;
}

struct Meta {}

parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.overflow);
        pkt.extract(hdr.underflow);
        pkt.extract(hdr.rshift);
        pkt.extract(hdr.lshift);
        pkt.extract(hdr.mod);
        pkt.extract(hdr.comp);
        pkt.extract(hdr.div);
        pkt.extract(hdr.b);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        //overflow
        h.overflow.a = 8w255 |+| 8w2;
        h.overflow.b = 8w3 |+| 8w0;
        //underflow
        h.underflow.a = 8w1 |-| 8w2;
        h.underflow.b = 8w3 |-| 8w0;
        const bit<8> uflow_tmp = 1;
        h.underflow.c = uflow_tmp |-| uflow_tmp;
        // unsigned mod
        h.mod.a = 4w1 % 4w8;
        h.mod.b = 4w15 % 4w2;
        // signed mod
        h.mod.c = 1 % 4w8;
        h.mod.d = 3 % 2;
        // // right shift
        bit<4> tmp = 4w0 - 4w1;
        h.rshift.a = tmp / 4w2;
        h.rshift.b = 4s7 >> 1 >> 1;
        h.rshift.c = 4w15 >> 1 >> 1;
        h.rshift.d = -4s7 >> 1 >> 1;
        h.rshift.e = tmp >> 1 >> 1;
        h.rshift.g = 4w1 >> 8w16;
        h.rshift.h = (bit<8>)~(4w1 >> 8w1);
        //left shift
        h.lshift.a = (bit<8>)(4w4 << 8w2);
        h.lshift.b = (bit<8>)(4w4 << 8w16);
        h.lshift.c = 1 << 1;
        h.lshift.d = (bit<8>)1 << 256;
        h.lshift.e = 8w1 << 8w0;

        // comparing various constants
        if (4w15  > 2) { h.comp.a = 1; }
        if (4w3  > 2) { h.comp.b = 1; }
        if (-1  > 4w8) { h.comp.c = 1; }
        if (4w8 > -1) { h.comp.d = 1; }
        // FIXME: This expression should also work
        // if (-1  > 4s8) { h.comp.e = 1; }
        if (-1  > 4s7) { h.comp.e = 1; }
        // Division
        h.div.a = (bit<8>)(4 / 1w1);
        h.div.b = (3 - 8w2 / 2);
        h.div.c = (8w2 / 2 - 3 );
        // nested int operations
        bit<48> tmp2 = (1 | 2) |+| 48w0;
        const int int_def = 1;

        // bool evaluation
        h.b.a = 1 == 1;
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out pkt, in Headers h) {
    apply {
        pkt.emit(h);
    }
}
V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;


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
header ethernet_t {
  bit<48> dst_addr;
  bit<48> src_addr;
  bit<16> eth_type;
}
header OVERFLOW {
  bit<8> a;
  bit<8> b;
}
header UNDERFLOW {
  bit<8> a;
  bit<8> b;
  bit<8> c;
}
header MOD {
  bit<4> a;
  bit<4> b;
  bit<4> c;
  bit<4> d;
}
header RSH {
  bit<4> a;
  int<4> b;
  bit<4> c;
  int<4> d;
  bit<4> e;
  bit<4> g;
  bit<8> h;
}
header LSH {
  bit<8> a;
  bit<8> b;
  bit<8> c;
  bit<8> d;
  bit<8> e;
}
header COMPARE {
  bit<8> a;
  bit<8> b;
  bit<8> c;
  bit<8> d;
  bit<8> e;
}
header DIV {
  bit<8> a;
  bit<8> b;
  bit<8> c;
}
header BOOL {
  bool a;
  bit<7> padding;
}
struct Headers {
  ethernet_t eth_hdr;
  OVERFLOW overflow;
  UNDERFLOW underflow;
  RSH rshift;
  LSH lshift;
  MOD mod;
  COMPARE comp;
  DIV div;
  BOOL b;
}
struct Meta {
  
}
parser p(packet_in pkt, out Headers hdr, inout Meta m,
         inout standard_metadata_t sm) {
  state start {
    transition parse_hdrs;
  }
  state parse_hdrs
    {
    pkt.extract(hdr.eth_hdr);
    pkt.extract(hdr.overflow);
    pkt.extract(hdr.underflow);
    pkt.extract(hdr.rshift);
    pkt.extract(hdr.lshift);
    pkt.extract(hdr.mod);
    pkt.extract(hdr.comp);
    pkt.extract(hdr.div);
    pkt.extract(hdr.b);
    transition accept;
  }
}
control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
  apply
    {
    h.overflow.a = 8w255|+|8w2;
    h.overflow.b = 8w3|+|8w0;
    h.underflow.a = 8w1|-|8w2;
    h.underflow.b = 8w3|-|8w0;
    const bit<8> uflow_tmp = 1;
    h.underflow.c = uflow_tmp|-|uflow_tmp;
    h.mod.a = 4w1%4w8;
    h.mod.b = 4w15%4w2;
    h.mod.c = 1%4w8;
    h.mod.d = 3%2;
    bit<4> tmp = 4w0-4w1;
    h.rshift.a = tmp/4w2;
    h.rshift.b = 4s7>>1>>1;
    h.rshift.c = 4w15>>1>>1;
    h.rshift.d = -4s7>>1>>1;
    h.rshift.e = tmp>>1>>1;
    h.rshift.g = 4w1>>8w16;
    h.rshift.h = (bit<8>) ~4w1>>8w1;
    h.lshift.a = (bit<8>) 4w4<<8w2;
    h.lshift.b = (bit<8>) 4w4<<8w16;
    h.lshift.c = 1<<1;
    h.lshift.d = (bit<8>) 1<<256;
    h.lshift.e = 8w1<<8w0;
    if (4w15>2) {
      h.comp.a = 1;
    }
    if (4w3>2) {
      h.comp.b = 1;
    }
    if (-1>4w8) {
      h.comp.c = 1;
    }
    if (4w8>-1) {
      h.comp.d = 1;
    }
    if (-1>4s7) {
      h.comp.e = 1;
    }
    h.div.a = (bit<8>) 4/1w1;
    h.div.b = 3-8w2/2;
    h.div.c = 8w2/2-3;
    bit<48> tmp2 = 1 | 2|+|48w0;
    const int int_def = 1;
    h.b.a = 1==1;
  }
}
control vrfy(inout Headers h, inout Meta m) {
  apply { 
  }
}
control update(inout Headers h, inout Meta m) {
  apply { 
  }
}
control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
  apply { 
  }
}
control deparser(packet_out pkt, in Headers h) {
  apply {
    pkt.emit(h);
  }
}
V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(120): [--Wwarn=overflow] warning: >>: Shifting 4-bit value with 16
        h.rshift.g = 4w1 >> 8w16;
                     ^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(123): [--Wwarn=mismatch] warning: 4w16: value does not fit in 4 bits
        h.lshift.a = (bit<8>)(4w4 << 8w2);
                              ^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(124): [--Wwarn=overflow] warning: <<: Shifting 4-bit value with 16
        h.lshift.b = (bit<8>)(4w4 << 8w16);
                              ^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(124): [--Wwarn=mismatch] warning: 4w262144: value does not fit in 4 bits
        h.lshift.b = (bit<8>)(4w4 << 8w16);
                              ^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(126): [--Wwarn=overflow] warning: <<: Shifting 8-bit value with 256
        h.lshift.d = (bit<8>)1 << 256;
                     ^^^^^^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(126): [--Wwarn=mismatch] warning: 8w115792089237316195423570985008687907853269984665640564039457584007913129639936: value does not fit in 8 bits
        h.lshift.d = (bit<8>)1 << 256;
                     ^^^^^^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(132): [--Wwarn=mismatch] warning: -4w1: negative value with unsigned type
        if (-1 > 4w8) { h.comp.c = 1; }
             ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(133): [--Wwarn=mismatch] warning: -4w1: negative value with unsigned type
        if (4w8 > -1) { h.comp.d = 1; }
                   ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_various_ops-bmv2.p4(138): [--Wwarn=mismatch] warning: 1w4: value does not fit in 1 bits
        h.div.a = (bit<8>)(4 / 1w1);
                           ^
