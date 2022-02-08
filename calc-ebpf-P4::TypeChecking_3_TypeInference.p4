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
    @name("tmp") bit<8> tmp_6;
    @name("tmp_1") p4calc_t tmp_7;
    @name("tmp_2") bit<8> tmp_8;
    @name("tmp_3") p4calc_t tmp_9;
    @name("tmp_4") bit<8> tmp_10;
    @name("tmp_5") p4calc_t tmp_11;
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        tmp_7 = packet.lookahead<p4calc_t>();
        tmp_6 = tmp_7.p;
        tmp_9 = packet.lookahead<p4calc_t>();
        tmp_8 = tmp_9.four;
        tmp_11 = packet.lookahead<p4calc_t>();
        tmp_10 = tmp_11.ver;
        transition select(tmp_6, tmp_8, tmp_10) {
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
    @name("tmp") bit<48> tmp_12;
    @name("operation_add") action operation_add_0() {
        tmp_12 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_12;
        hdr.p4calc.res = hdr.p4calc.operand_a + hdr.p4calc.operand_b;
    }
    @name("operation_sub") action operation_sub_0() {
        tmp_12 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_12;
        hdr.p4calc.res = hdr.p4calc.operand_a - hdr.p4calc.operand_b;
    }
    @name("operation_and") action operation_and_0() {
        tmp_12 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_12;
        hdr.p4calc.res = hdr.p4calc.operand_a & hdr.p4calc.operand_b;
    }
    @name("operation_or") action operation_or_0() {
        tmp_12 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_12;
        hdr.p4calc.res = hdr.p4calc.operand_a | hdr.p4calc.operand_b;
    }
    @name("operation_xor") action operation_xor_0() {
        tmp_12 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_12;
        hdr.p4calc.res = hdr.p4calc.operand_a ^ hdr.p4calc.operand_b;
    }
    @name("operation_drop") action operation_drop_0() {
        xout = false;
    }
    @name("operation_drop") action operation_drop_2() {
        xout = false;
    }
    @name("calculate") table calculate {
        key = {
            hdr.p4calc.op: exact @name("hdr.p4calc.op") ;
        }
        actions = {
            operation_add_0();
            operation_sub_0();
            operation_and_0();
            operation_or_0();
            operation_xor_0();
            operation_drop_0();
        }
        const default_action = operation_drop_0();
        const entries = {
                        8w0x2b : operation_add_0();
                        8w0x2d : operation_sub_0();
                        8w0x26 : operation_and_0();
                        8w0x7c : operation_or_0();
                        8w0x5e : operation_xor_0();
        }
        implementation = hash_table(32w8);
    }
    apply {
        xout = true;
        if (hdr.p4calc.isValid()) {
            calculate.apply();
        } else {
            operation_drop_2();
        }
    }
}

ebpfFilter<headers>(Parser(), Ingress()) main;

