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

extern CounterArray {
    CounterArray(bit<32> max_index, bool sparse);
    void increment(in bit<32> index);
    void add(in bit<32> index, in bit<32> value);
}

extern array_table {
    array_table(bit<32> size);
}

extern hash_table {
    hash_table(bit<32> size);
}

parser parse<H>(packet_in packet, out H headers);
control filter<H>(inout H headers, out bool accept);
package ebpfFilter<H>(parse<H> prs, filter<H> filt);
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

parser Parser(packet_in packet, out headers hdr) {
    @name("tmp") bit<8> tmp;
    @name("tmp_1") p4calc_t tmp_0;
    @name("tmp_2") bit<8> tmp_1;
    @name("tmp_3") p4calc_t tmp_2;
    @name("tmp_4") bit<8> tmp_3;
    @name("tmp_5") p4calc_t tmp_4;
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        tmp_0 = packet.lookahead<p4calc_t>();
        tmp = tmp_0.p;
        tmp_2 = packet.lookahead<p4calc_t>();
        tmp_1 = tmp_2.four;
        tmp_4 = packet.lookahead<p4calc_t>();
        tmp_3 = tmp_4.ver;
        transition select(tmp, tmp_1, tmp_3) {
            (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
            default: accept;
        }
    }
    state parse_p4calc {
        packet.extract<p4calc_t>(hdr.p4calc);
        transition accept;
    }
}

control Ingress(inout headers hdr, out bool xout) {
    @name("tmp") bit<48> tmp_5;
    @name("operation_add") action operation_add() {
        tmp_5 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_5;
        hdr.p4calc.res = hdr.p4calc.operand_a + hdr.p4calc.operand_b;
    }
    @name("operation_sub") action operation_sub() {
        tmp_5 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_5;
        hdr.p4calc.res = hdr.p4calc.operand_a - hdr.p4calc.operand_b;
    }
    @name("operation_and") action operation_and() {
        tmp_5 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_5;
        hdr.p4calc.res = hdr.p4calc.operand_a & hdr.p4calc.operand_b;
    }
    @name("operation_or") action operation_or() {
        tmp_5 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_5;
        hdr.p4calc.res = hdr.p4calc.operand_a | hdr.p4calc.operand_b;
    }
    @name("operation_xor") action operation_xor() {
        tmp_5 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_5;
        hdr.p4calc.res = hdr.p4calc.operand_a ^ hdr.p4calc.operand_b;
    }
    @name("operation_drop") action operation_drop() {
        xout = false;
    }
    @name("operation_drop") action operation_drop_1() {
        xout = false;
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
            operation_drop();
        }
        const default_action = operation_drop();
        const entries = {
                        8w0x2b : operation_add();
                        8w0x2d : operation_sub();
                        8w0x26 : operation_and();
                        8w0x7c : operation_or();
                        8w0x5e : operation_xor();
        }
        implementation = hash_table(32w8);
    }
    apply {
        xout = true;
        if (hdr.p4calc.isValid()) {
            calculate_0.apply();
        } else {
            operation_drop_1();
        }
    }
}

ebpfFilter<headers>(Parser(), Ingress()) main;

