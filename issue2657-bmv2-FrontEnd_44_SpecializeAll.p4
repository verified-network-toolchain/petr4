error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument
}

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

match_kind {
    exact,
    ternary,
    lpm
}

match_kind {
    range,
    optional,
    selector
}

const bit<32> __v1model_version = 32w20200408;
typedef bit<9> PortId_t;
@metadata @name("standard_metadata") struct standard_metadata_t {
    PortId_t ingress_port;
    PortId_t egress_spec;
    PortId_t egress_port;
    bit<32>  instance_type;
    bit<32>  packet_length;
    @alias("queueing_metadata.enq_timestamp") 
    bit<32>  enq_timestamp;
    @alias("queueing_metadata.enq_qdepth") 
    bit<19>  enq_qdepth;
    @alias("queueing_metadata.deq_timedelta") 
    bit<32>  deq_timedelta;
    @alias("queueing_metadata.deq_qdepth") 
    bit<19>  deq_qdepth;
    @alias("intrinsic_metadata.ingress_global_timestamp") 
    bit<48>  ingress_global_timestamp;
    @alias("intrinsic_metadata.egress_global_timestamp") 
    bit<48>  egress_global_timestamp;
    @alias("intrinsic_metadata.mcast_grp") 
    bit<16>  mcast_grp;
    @alias("intrinsic_metadata.egress_rid") 
    bit<16>  egress_rid;
    bit<1>   checksum_error;
    error    parser_error;
    @alias("intrinsic_metadata.priority") 
    bit<3>   priority;
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

extern meter<I> {
    meter(bit<32> size, MeterType type);
    void execute_meter<T>(in I index, out T result);
}

extern direct_meter<T> {
    direct_meter(MeterType type);
    void read(out T result);
}

extern register<T, I> {
    register(bit<32> size);
    @noSideEffects void read(out T result, in I index);
    void write(in I index, in T value);
}

extern action_profile {
    action_profile(bit<32> size);
}

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

@pure extern void hash<O, T, D, M>(out O result, in HashAlgorithm algo, in T base, in D data, in M max);
extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
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
    @name("tmp") bit<16> tmp_0;
    apply {
        hash<bit<16>, bit<9>, tuple_0, bit<18>>(tmp_0, HashAlgorithm.crc32, 9w0, (tuple_0){tmp1 = pkt.ethernet.etherType}, 18w512);
        pkt.ethernet.etherType = tmp_0;
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

