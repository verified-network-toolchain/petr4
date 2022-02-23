/petr4/ci-test/type-checking/testdata/p4_16_samples/basic_routing-bmv2.p4
\n
#include <core.p4>
#include <v1model.p4>

struct ingress_metadata_t {
    bit<12> vrf;
    bit<16> bd;
    bit<16> nexthop_index;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
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

struct metadata {
    ingress_metadata_t ingress_metadata;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state parse_ethernet {
        packet.extract(hdr = hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract(hdr = hdr.ipv4);
        transition accept;
    }
    state start {
        transition parse_ethernet;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action on_miss() {
    }
    action rewrite_src_dst_mac(bit<48> smac, bit<48> dmac) {
        hdr.ethernet.srcAddr = smac;
        hdr.ethernet.dstAddr = dmac;
    }
    table rewrite_mac {
        actions = {
            on_miss;
            rewrite_src_dst_mac;
        }
        key = {
            meta.ingress_metadata.nexthop_index: exact;
        }
        size = 32768;
    }
    apply {
        rewrite_mac.apply();
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action set_vrf(bit<12> vrf) {
        meta.ingress_metadata.vrf = vrf;
    }
    action on_miss() {
    }
    action fib_hit_nexthop(bit<16> nexthop_index) {
        meta.ingress_metadata.nexthop_index = nexthop_index;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 8w1;
    }
    action set_egress_details(bit<9> egress_spec) {
        standard_metadata.egress_spec = egress_spec;
    }
    action set_bd(bit<16> bd) {
        meta.ingress_metadata.bd = bd;
    }
    table bd {
        actions = {
            set_vrf;
        }
        key = {
            meta.ingress_metadata.bd: exact;
        }
        size = 65536;
    }
    table ipv4_fib {
        actions = {
            on_miss;
            fib_hit_nexthop;
        }
        key = {
            meta.ingress_metadata.vrf: exact;
            hdr.ipv4.dstAddr         : exact;
        }
        size = 131072;
    }
    table ipv4_fib_lpm {
        actions = {
            on_miss;
            fib_hit_nexthop;
        }
        key = {
            meta.ingress_metadata.vrf: exact;
            hdr.ipv4.dstAddr         : lpm;
        }
        size = 16384;
    }
    table nexthop {
        actions = {
            on_miss;
            set_egress_details;
        }
        key = {
            meta.ingress_metadata.nexthop_index: exact;
        }
        size = 32768;
    }
    table port_mapping {
        actions = {
            set_bd;
        }
        key = {
            standard_metadata.ingress_port: exact;
        }
        size = 32768;
    }
    apply {
        if (hdr.ipv4.isValid()) {
            port_mapping.apply();
            bd.apply();
            switch (ipv4_fib.apply().action_run) {
                on_miss: {
                    ipv4_fib_lpm.apply();
                }
            }

            nexthop.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr = hdr.ethernet);
        packet.emit(hdr = hdr.ipv4);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum(
        data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr },
        checksum = hdr.ipv4.hdrChecksum,
        condition = true,
        algo = HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum(
        condition = true,
        data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr },
        algo = HashAlgorithm.csum16,
        checksum = hdr.ipv4.hdrChecksum);
    }
}

V1Switch(p = ParserImpl(),
         ig = ingress(),
         vr = verifyChecksum(),
         eg = egress(),
         ck = computeChecksum(),
         dep = DeparserImpl()) main;
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
struct ingress_metadata_t {
  bit<12> vrf;
  bit<16> bd;
  bit<16> nexthop_index;
}
header ethernet_t {
  bit<48> dstAddr;
  bit<48> srcAddr;
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
struct metadata {
  ingress_metadata_t ingress_metadata;
}
struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  state parse_ethernet
    {
    packet.extract(hdr=hdr.ethernet);
    transition select(hdr.ethernet.etherType) {
      16w2048: parse_ipv4;
      default: accept;
    }
  }
  state parse_ipv4 {
    packet.extract(hdr=hdr.ipv4);
    transition accept;
  }
  state start {
    transition parse_ethernet;
  }
}
control egress(inout headers hdr, inout metadata meta,
               inout standard_metadata_t standard_metadata) {
  action on_miss() { 
  }
  action rewrite_src_dst_mac(bit<48> smac, bit<48> dmac)
    {
    hdr.ethernet.srcAddr = smac;
    hdr.ethernet.dstAddr = dmac;
  }
  table rewrite_mac
    {
    actions = {
      on_miss;rewrite_src_dst_mac;
    }
    key = {
      meta.ingress_metadata.nexthop_index: exact;
    }
    size = 32768;
  }
  apply {
    rewrite_mac.apply();
  }
}
control ingress(inout headers hdr, inout metadata meta,
                inout standard_metadata_t standard_metadata) {
  action set_vrf(bit<12> vrf) {
    meta.ingress_metadata.vrf = vrf;
  }
  action on_miss() { 
  }
  action fib_hit_nexthop(bit<16> nexthop_index)
    {
    meta.ingress_metadata.nexthop_index = nexthop_index;
    hdr.ipv4.ttl = hdr.ipv4.ttl-8w1;
  }
  action set_egress_details(bit<9> egress_spec)
    {
    standard_metadata.egress_spec = egress_spec;
  }
  action set_bd(bit<16> bd) {
    meta.ingress_metadata.bd = bd;
  }
  table bd
    {
    actions = {
      set_vrf;
    }
    key = {
      meta.ingress_metadata.bd: exact;
    }
    size = 65536;
  }
  table ipv4_fib
    {
    actions = {
      on_miss;fib_hit_nexthop;
    }
    key = {
      meta.ingress_metadata.vrf: exact;
      hdr.ipv4.dstAddr: exact;
    }
    size = 131072;
  }
  table ipv4_fib_lpm
    {
    actions = {
      on_miss;fib_hit_nexthop;
    }
    key = {
      meta.ingress_metadata.vrf: exact;
      hdr.ipv4.dstAddr: lpm;
    }
    size = 16384;
  }
  table nexthop
    {
    actions = {
      on_miss;set_egress_details;
    }
    key = {
      meta.ingress_metadata.nexthop_index: exact;
    }
    size = 32768;
  }
  table port_mapping
    {
    actions = {
      set_bd;
    }
    key = {
      standard_metadata.ingress_port: exact;
    }
    size = 32768;
  }
  apply
    {
    if (hdr.ipv4.isValid()) {
      port_mapping.apply();
      bd.apply();
      switch (ipv4_fib.apply().action_run) {
      on_miss: {
      ipv4_fib_lpm.apply();
      }
      }
      nexthop.apply();
    }
  }
}
control DeparserImpl(packet_out packet, in headers hdr) {
  apply {
    packet.emit(hdr=hdr.ethernet);
    packet.emit(hdr=hdr.ipv4);
  }
}
control verifyChecksum(inout headers hdr, inout metadata meta) {
  apply
    {
    verify_checksum(data={hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv,
                           hdr.ipv4.totalLen, hdr.ipv4.identification,
                           hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl,
                           hdr.ipv4.protocol, hdr.ipv4.srcAddr,
                           hdr.ipv4.dstAddr},
                      checksum=hdr.ipv4.hdrChecksum, condition=true,
                      algo=HashAlgorithm.csum16);
  }
}
control computeChecksum(inout headers hdr, inout metadata meta) {
  apply
    {
    update_checksum(condition=true,
                      data={hdr.ipv4.version, hdr.ipv4.ihl,
                             hdr.ipv4.diffserv, hdr.ipv4.totalLen,
                             hdr.ipv4.identification, hdr.ipv4.flags,
                             hdr.ipv4.fragOffset, hdr.ipv4.ttl,
                             hdr.ipv4.protocol, hdr.ipv4.srcAddr,
                             hdr.ipv4.dstAddr},
                      algo=HashAlgorithm.csum16,
                      checksum=hdr.ipv4.hdrChecksum);
  }
}
V1Switch(p=ParserImpl(), ig=ingress(), vr=verifyChecksum(), eg=egress(),
           ck=computeChecksum(), dep=DeparserImpl())
  main;

************************\n******** p4c type checking result: ********\n************************\n
