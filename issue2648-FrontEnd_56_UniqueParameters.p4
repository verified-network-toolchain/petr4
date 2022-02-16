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

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
}

struct Headers {
    ethernet_t eth_hdr;
    H[2]       h;
}

bit<8> give_value(H dummy_hdr) {
    @name("hasReturned") bool hasReturned_0 = false;
    @name("retval") bit<8> retval_0;
    {
        hasReturned_0 = true;
        retval_0 = dummy_hdr.a;
    }
    return retval_0;
}
parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    apply {
        tmp_1 = give_value((H){a = 8w1});
        tmp_2 = tmp_1;
        h.h[tmp_2].a = 8w1;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

