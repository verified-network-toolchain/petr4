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

enum CloneType {
    I2E,
    E2E
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

extern void log_msg<T>(string msg, in T data);
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

struct headers_t {
    ethernet_t ethernet;
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

enum MyEnum_t {
    VAL1,
    VAL2,
    VAL3
}

enum bit<10> MySerializableEnum_t {
    VAL17 = 10w17,
    VAL23 = 10w23,
    VAL19 = 10w19
}

control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    bool bool1;
    bit<1> bit1;
    MyEnum_t enum1;
    MySerializableEnum_t serenum1;
    int<8> signed1;
    bit<8> unsigned1;
    apply {
        bool1 = (bool)hdr.ethernet.dstAddr[0:0];
        log_msg<tuple<bool>>("bool1={}", { bool1 });
        log_msg<tuple<bit<1>>>("(bit<1>) bool1={}", { (bit<1>)bool1 });
        log_msg<tuple<bit<1>>>("(bit<1>) (!bool1)={}", { (bit<1>)!bool1 });
        bit1 = hdr.ethernet.dstAddr[0:0];
        log_msg<tuple<bit<1>>>("bit1={}", { bit1 });
        signed1 = 8s127;
        signed1 = signed1 + 8s1;
        log_msg<tuple<int<8>>>("signed1={}", { signed1 });
        unsigned1 = 8w127;
        unsigned1 = unsigned1 + 8w1;
        log_msg<tuple<bit<8>>>("unsigned1={}", { unsigned1 });
        if (hdr.ethernet.dstAddr[1:0] == 2w0) {
            enum1 = MyEnum_t.VAL1;
        } else if (hdr.ethernet.dstAddr[1:0] == 2w1) {
            enum1 = MyEnum_t.VAL2;
        } else {
            enum1 = MyEnum_t.VAL3;
        }
        log_msg<tuple<MyEnum_t>>("enum1={}", { enum1 });
        if (hdr.ethernet.dstAddr[1:0] == 2w0) {
            serenum1 = MySerializableEnum_t.VAL17;
        } else if (hdr.ethernet.dstAddr[1:0] == 2w1) {
            serenum1 = MySerializableEnum_t.VAL23;
        } else {
            serenum1 = MySerializableEnum_t.VAL19;
        }
        log_msg<tuple<MySerializableEnum_t>>("serenum1={}", { serenum1 });
        log_msg<tuple<ethernet_t>>("hdr.ethernet={}", { hdr.ethernet });
        log_msg<tuple<standard_metadata_t>>("stdmeta={}", { stdmeta });
        log_msg<tuple<error>>("error.PacketTooShort={}", { error.PacketTooShort });
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

