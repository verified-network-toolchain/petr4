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

const bit<32> __v1model_version = 32w20180101;
@metadata @name("standard_metadata") struct standard_metadata_t {
    bit<9>  ingress_port;
    bit<9>  egress_spec;
    bit<9>  egress_port;
    bit<32> instance_type;
    bit<32> packet_length;
    @alias("queueing_metadata.enq_timestamp") 
    bit<32> enq_timestamp;
    @alias("queueing_metadata.enq_qdepth") 
    bit<19> enq_qdepth;
    @alias("queueing_metadata.deq_timedelta") 
    bit<32> deq_timedelta;
    @alias("queueing_metadata.deq_qdepth") 
    bit<19> deq_qdepth;
    @alias("intrinsic_metadata.ingress_global_timestamp") 
    bit<48> ingress_global_timestamp;
    @alias("intrinsic_metadata.egress_global_timestamp") 
    bit<48> egress_global_timestamp;
    @alias("intrinsic_metadata.mcast_grp") 
    bit<16> mcast_grp;
    @alias("intrinsic_metadata.egress_rid") 
    bit<16> egress_rid;
    bit<1>  checksum_error;
    error   parser_error;
    @alias("intrinsic_metadata.priority") 
    bit<3>  priority;
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
    void execute_meter<T>(in bit<32> index, out T result);
}

extern direct_meter<T> {
    direct_meter(MeterType type);
    void read(out T result);
}

extern register<T> {
    register(bit<32> size);
    @noSideEffects void read(out T result, in bit<32> index);
    void write(in bit<32> index, in T value);
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
struct meta_t {
}

header eth_h {
    bit<48> dst;
    bit<48> src;
    bit<16> type;
}

header ipv4_h {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  tos;
    bit<16> len;
    bit<16> id;
    bit<3>  flags;
    bit<13> frag;
    bit<8>  ttl;
    bit<8>  proto;
    bit<16> chksum;
    bit<32> src;
    bit<32> dst;
}

struct headers_t {
    eth_h  eth;
    ipv4_h ipv4;
}

parser InnerParser(packet_in pkt, out headers_t hdr) {
    state start {
        transition parse_eth;
    }
    state parse_eth {
        pkt.extract<eth_h>(hdr.eth);
        transition select(hdr.eth.type) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        pkt.extract<ipv4_h>(hdr.ipv4);
        transition accept;
    }
}

parser OuterParser(packet_in pkt, out headers_t hdr, inout meta_t m, inout standard_metadata_t meta) {
    @name("InnerParser") InnerParser() InnerParser_inst;
    state start {
        InnerParser_inst.apply(pkt, hdr);
        transition accept;
    }
}

control NoVerify(inout headers_t hdr, inout meta_t m) {
    apply {
    }
}

control NoCheck(inout headers_t hdr, inout meta_t m) {
    apply {
    }
}

control NoIngress(inout headers_t hdr, inout meta_t m, inout standard_metadata_t meta) {
    apply {
    }
}

control NoEgress(inout headers_t hdr, inout meta_t m, inout standard_metadata_t meta) {
    apply {
    }
}

control SimpleDeparser(packet_out pkt, in headers_t hdr) {
    apply {
        pkt.emit<eth_h>(hdr.eth);
        pkt.emit<ipv4_h>(hdr.ipv4);
    }
}

V1Switch<headers_t, meta_t>(OuterParser(), NoVerify(), NoIngress(), NoEgress(), NoCheck(), SimpleDeparser()) main;

