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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
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

extern void random<T>(out T result, in T lo, in T hi);
extern void digest<T>(in bit<32> receiver, in T data);
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

@deprecated("Please use mark_to_drop(standard_metadata) instead.") extern void mark_to_drop();
@pure extern void mark_to_drop(inout standard_metadata_t standard_metadata);
@pure extern void hash<O, T, D, M>(out O result, in HashAlgorithm algo, in T base, in D data, in M max);
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

extern void verify_checksum<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
extern void verify_checksum_with_payload<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@noSideEffects extern void update_checksum_with_payload<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead") extern void resubmit<T>(in T data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead") extern void recirculate<T>(in T data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead") extern void clone3<T>(in CloneType type, in bit<32> session, in T data);
extern void clone_preserving_field_list(in CloneType type, in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T>(string msg, in T data);
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

const bit<16> P4CALC_ETYPE = 16w0x1234;
const bit<8> P4CALC_P = 8w0x50;
const bit<8> P4CALC_4 = 8w0x34;
const bit<8> P4CALC_VER = 8w0x1;
const bit<8> P4CALC_PLUS = 8w0x2b;
const bit<8> P4CALC_MINUS = 8w0x2d;
const bit<8> P4CALC_AND = 8w0x26;
const bit<8> P4CALC_OR = 8w0x7c;
const bit<8> P4CALC_CARET = 8w0x5e;
const bit<8> P4CALC_CRC = 8w0x3e;
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
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        transition select((packet.lookahead<p4calc_t>()).p, (packet.lookahead<p4calc_t>()).four, (packet.lookahead<p4calc_t>()).ver) {
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
    action send_back(bit<32> result) {
        bit<48> tmp;
        hdr.p4calc.res = result;
        tmp = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp;
        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }
    action operation_add() {
        send_back(hdr.p4calc.operand_a + hdr.p4calc.operand_b);
    }
    action operation_sub() {
        send_back(hdr.p4calc.operand_a - hdr.p4calc.operand_b);
    }
    action operation_and() {
        send_back(hdr.p4calc.operand_a & hdr.p4calc.operand_b);
    }
    action operation_or() {
        send_back(hdr.p4calc.operand_a | hdr.p4calc.operand_b);
    }
    action operation_xor() {
        send_back(hdr.p4calc.operand_a ^ hdr.p4calc.operand_b);
    }
    action operation_crc() {
        bit<32> nbase = hdr.p4calc.operand_b;
        bit<64> ncount = 64w8589934592;
        bit<32> nselect;
        bit<32> ninput = hdr.p4calc.operand_a;
        hash<bit<32>, bit<32>, tuple<bit<32>>, bit<64>>(nselect, HashAlgorithm.crc32, nbase, { ninput }, ncount);
        send_back(nselect);
    }
    action operation_drop() {
        mark_to_drop(standard_metadata);
    }
    table calculate {
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
            calculate.apply();
        } else {
            operation_drop();
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

