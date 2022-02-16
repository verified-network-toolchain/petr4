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

@pure extern void mark_to_drop(inout standard_metadata_t standard_metadata);
@pure extern void hash<O, T, D, M>(out O result, in HashAlgorithm algo, in T base, in D data, in M max);
extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
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

header p4calc_t {
    bit<8>  p;
    bit<8>  four;
    bit<8>  ver;
    bit<8>  op;
    bit<32> operand_a;
    bit<32> operand_b;
    bit<32> res;
}

struct headers {
    ethernet_t ethernet;
    p4calc_t   p4calc;
}

struct metadata {
}

parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<8> tmp;
    p4calc_t tmp_1;
    bit<8> tmp_2;
    p4calc_t tmp_3;
    bit<8> tmp_4;
    p4calc_t tmp_5;
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        tmp_1 = packet.lookahead<p4calc_t>();
        tmp = tmp_1.p;
        tmp_3 = packet.lookahead<p4calc_t>();
        tmp_2 = tmp_3.four;
        tmp_5 = packet.lookahead<p4calc_t>();
        tmp_4 = tmp_5.ver;
        transition select(tmp, tmp_2, tmp_4) {
            (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
            default: accept;
        }
    }
    state parse_p4calc {
        packet.extract<p4calc_t>(hdr.p4calc);
        transition accept;
    }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("tmp") bit<48> tmp_0;
    @name("nbase") bit<32> nbase_0;
    @name("ncount") bit<64> ncount_0;
    @name("nselect") bit<32> nselect_0;
    @name("ninput") bit<32> ninput_0;
    @name("operation_add") action operation_add() {
        {
            hdr.p4calc.res = hdr.p4calc.operand_a + hdr.p4calc.operand_b;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_sub") action operation_sub() {
        {
            hdr.p4calc.res = hdr.p4calc.operand_a - hdr.p4calc.operand_b;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_and") action operation_and() {
        {
            hdr.p4calc.res = hdr.p4calc.operand_a & hdr.p4calc.operand_b;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_or") action operation_or() {
        {
            hdr.p4calc.res = hdr.p4calc.operand_a | hdr.p4calc.operand_b;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_xor") action operation_xor() {
        {
            hdr.p4calc.res = hdr.p4calc.operand_a ^ hdr.p4calc.operand_b;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_crc") action operation_crc() {
        nbase_0 = hdr.p4calc.operand_b;
        ncount_0 = 64w8589934592;
        ninput_0 = hdr.p4calc.operand_a;
        hash<bit<32>, bit<32>, tuple<bit<32>>, bit<64>>(nselect_0, HashAlgorithm.crc32, nbase_0, { ninput_0 }, ncount_0);
        {
            hdr.p4calc.res = nselect_0;
            tmp_0 = hdr.ethernet.dstAddr;
            hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
            hdr.ethernet.srcAddr = tmp_0;
            standard_metadata.egress_spec = standard_metadata.ingress_port;
        }
    }
    @name("operation_drop") action operation_drop() {
        mark_to_drop(standard_metadata);
    }
    @name("operation_drop") action operation_drop_1() {
        mark_to_drop(standard_metadata);
    }
    @name("calculate") table calculate_0 {
        key = {
            hdr.p4calc.op: exact @name("hdr.p4calc.op") ;
        }
        actions = {
            operation_add();
            operation_sub();
            operation_and();
            operation_or();
            operation_xor();
            operation_crc();
            operation_drop();
        }
        const default_action = operation_drop();
        const entries = {
                        8w0x2b : operation_add();
                        8w0x2d : operation_sub();
                        8w0x26 : operation_and();
                        8w0x7c : operation_or();
                        8w0x5e : operation_xor();
                        8w0x3e : operation_crc();
        }
    }
    apply {
        if (hdr.p4calc.isValid()) {
            calculate_0.apply();
        } else {
            operation_drop_1();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum<tuple<bit<32>>, bit<32>>(hdr.p4calc.isValid(), { hdr.p4calc.operand_a }, hdr.p4calc.res, HashAlgorithm.crc32);
    }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<p4calc_t>(hdr.p4calc);
    }
}

V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;

