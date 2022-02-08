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

const bit<16> P4CALC_ETYPE = 0x1234;
const bit<8> P4CALC_P = 0x50;
const bit<8> P4CALC_4 = 0x34;
const bit<8> P4CALC_VER = 0x1;
const bit<8> P4CALC_PLUS = 0x2b;
const bit<8> P4CALC_MINUS = 0x2d;
const bit<8> P4CALC_AND = 0x26;
const bit<8> P4CALC_OR = 0x7c;
const bit<8> P4CALC_CARET = 0x5e;
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
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            P4CALC_ETYPE: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        transition select((packet.lookahead<p4calc_t>()).p, (packet.lookahead<p4calc_t>()).four, (packet.lookahead<p4calc_t>()).ver) {
            (P4CALC_P, P4CALC_4, P4CALC_VER): parse_p4calc;
            default: accept;
        }
    }
    state parse_p4calc {
        packet.extract(hdr.p4calc);
        transition accept;
    }
}

control Ingress(inout headers hdr, out bool xout) {
    action send_back(bit<32> result) {
        bit<48> tmp;
        tmp = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp;
        hdr.p4calc.res = result;
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
    action operation_drop() {
        xout = false;
    }
    table calculate {
        key = {
            hdr.p4calc.op: exact;
        }
        actions = {
            operation_add;
            operation_sub;
            operation_and;
            operation_or;
            operation_xor;
            operation_drop;
        }
        const default_action = operation_drop();
        const entries = {
                        P4CALC_PLUS : operation_add();
                        P4CALC_MINUS : operation_sub();
                        P4CALC_AND : operation_and();
                        P4CALC_OR : operation_or();
                        P4CALC_CARET : operation_xor();
        }
        implementation = hash_table(8);
    }
    apply {
        xout = true;
        if (hdr.p4calc.isValid()) {
            calculate.apply();
        } else {
            operation_drop();
        }
    }
}

ebpfFilter(Parser(), Ingress()) main;

