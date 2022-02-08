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

bit<3> max(in bit<3> val, in bit<3> bound) {
    bit<3> tmp;
    {
        if (val < bound) {
            tmp = val;
        } else {
            tmp = bound;
        }
        return tmp;
    }
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

extern bit<8> extern_call(inout H val);
parser p(packet_in pkt, out Headers hdr) {
    @name("tmp") H tmp_0;
    bit<8> tmp_1;
    bit<3> tmp_2;
    bit<3> tmp_3;
    H tmp_4;
    bit<8> tmp_5;
    state start {
        {
            tmp_2 = max(3w1, 3w2);
            tmp_3 = tmp_2;
            tmp_4 = hdr.h[tmp_3];
            tmp_5 = extern_call(tmp_4);
            hdr.h[tmp_3] = tmp_4;
            tmp_1 = tmp_5;
            tmp_0 = (H){a = tmp_1};
        }
        transition start_0;
    }
    state start_0 {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        pkt.extract<H>(hdr.h.next);
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

