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

extern void log_msg(string msg);
parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header H {
    bit<8> x;
}

header_union U {
    H h;
}

struct headers_t {
    ethernet_t ethernet;
    H          h1;
    U          u1;
}

struct metadata_t {
}

parser parserImpl(packet_in packet, out headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition accept;
    }
}

control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}

control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    @name("tmp") H tmp;
    @name("tmp_0") bool tmp_0;
    @name("tmp_1") U tmp_1;
    @name("tmp_2") bool tmp_2;
    @name("tmp_3") H[1] tmp_3;
    @name("tmp_4") bool tmp_4;
    @name("hasReturned") bool hasReturned;
    @name("retval") H retval;
    @name("h") H h_0;
    @name("hasReturned_0") bool hasReturned_0;
    @name("retval_0") U retval_0;
    @name("u") U u_0;
    @name("hasReturned_1") bool hasReturned_1;
    @name("retval_1") H[1] retval_1;
    @name("s") H[1] s_0;
    apply {
        if (hdr.ethernet.isValid()) {
            log_msg("hdr.ethernet is valid");
        } else {
            log_msg("hdr.ethernet is invalid");
        }
        hasReturned = false;
        h_0.setInvalid();
        hasReturned = true;
        retval = h_0;
        tmp = retval;
        tmp_0 = tmp.isValid();
        if (tmp_0) {
            log_msg("f() returned a valid header");
        } else {
            log_msg("f() returned an invalid header");
        }
        hasReturned_0 = false;
        u_0.h.setInvalid();
        hasReturned_0 = true;
        retval_0 = u_0;
        tmp_1 = retval_0;
        tmp_2 = tmp_1.h.isValid();
        if (tmp_2) {
            log_msg("g() returned a header_union with valid member h");
        } else {
            log_msg("g() returned a header_union with invalid member h");
        }
        hasReturned_1 = false;
        s_0[0].setInvalid();
        hasReturned_1 = true;
        retval_1 = s_0;
        tmp_3 = retval_1;
        tmp_4 = tmp_3[0].isValid();
        if (tmp_4) {
            log_msg("h() returned a header stack with valid element 0");
        } else {
            log_msg("h() returned a header stack with invalid element 0");
        }
    }
}

control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

control updateChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}

control deparserImpl(packet_out packet, in headers_t hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
    }
}

V1Switch<headers_t, metadata_t>(parserImpl(), verifyChecksum(), ingressImpl(), egressImpl(), updateChecksum(), deparserImpl()) main;

