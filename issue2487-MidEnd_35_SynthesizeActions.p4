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
}

control ingress(inout Headers h) {
    @name("ingress.tmp") ethernet_t tmp;
    @hidden action issue2487l19() {
        tmp.setValid();
        tmp.dst_addr = 48w1;
        tmp.src_addr = 48w1;
        tmp.eth_type = 16w1;
    }
    @hidden action issue2487l19_0() {
        tmp.setValid();
        tmp.dst_addr = 48w2;
        tmp.src_addr = 48w2;
        tmp.eth_type = 16w2;
    }
    @hidden action issue2487l19_1() {
        h.eth_hdr = tmp;
    }
    apply {
        if (h.eth_hdr.eth_type == 16w1) {
            issue2487l19();
        } else {
            issue2487l19_0();
        }
        issue2487l19_1();
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

