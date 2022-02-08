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
header addr_type_t {
    bit<8> dstType;
    bit<8> srcType;
}

header addr_ipv4_t {
    bit<32> addr;
}

header addr_ipv6_t {
    bit<128> addr;
}

header_union addr_t {
    addr_ipv4_t ipv4;
    addr_ipv6_t ipv6;
}

struct metadata {
}

struct headers {
    addr_type_t addr_type;
    addr_t      addr_dst;
    addr_t      addr_src;
}

parser ProtParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("ProtParser.addrType_0") bit<8> addrType_0;
    @name("ProtParser.addr_0") addr_t addr_0;
    state start {
        packet.extract<addr_type_t>(hdr.addr_type);
        addrType_0 = hdr.addr_type.dstType;
        addr_0.ipv4.setInvalid();
        addr_0.ipv6.setInvalid();
        transition ProtAddrParser_start;
    }
    state ProtAddrParser_start {
        transition select(addrType_0) {
            8w0x1: ProtAddrParser_ipv4;
            8w0x2: ProtAddrParser_ipv6;
            default: noMatch;
        }
    }
    state ProtAddrParser_ipv4 {
        packet.extract<addr_ipv4_t>(addr_0.ipv4);
        transition start_0;
    }
    state ProtAddrParser_ipv6 {
        packet.extract<addr_ipv6_t>(addr_0.ipv6);
        transition start_0;
    }
    state start_0 {
        hdr.addr_dst = addr_0;
        addrType_0 = hdr.addr_type.srcType;
        addr_0.ipv4.setInvalid();
        addr_0.ipv6.setInvalid();
        transition ProtAddrParser_start_0;
    }
    state ProtAddrParser_start_0 {
        transition select(addrType_0) {
            8w0x1: ProtAddrParser_ipv4_0;
            8w0x2: ProtAddrParser_ipv6_0;
            default: noMatch;
        }
    }
    state ProtAddrParser_ipv4_0 {
        packet.extract<addr_ipv4_t>(addr_0.ipv4);
        transition start_1;
    }
    state ProtAddrParser_ipv6_0 {
        packet.extract<addr_ipv6_t>(addr_0.ipv6);
        transition start_1;
    }
    state start_1 {
        hdr.addr_src = addr_0;
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control ProtVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control ProtIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control ProtEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control ProtComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control ProtDeparser(packet_out packet, in headers hdr) {
    apply {
        {
            packet.emit<addr_type_t>(hdr.addr_type);
            packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
            packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
            packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
            packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
        }
    }
}

V1Switch<headers, metadata>(ProtParser(), ProtVerifyChecksum(), ProtIngress(), ProtEgress(), ProtComputeChecksum(), ProtDeparser()) main;

