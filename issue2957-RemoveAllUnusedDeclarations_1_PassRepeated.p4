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

extern bit<8> extern_call(inout H val);
parser p(packet_in pkt, out Headers hdr) {
    @name("tmp_2") bit<3> tmp_1;
    @name("tmp_3") bit<3> tmp_6;
    @name("tmp_4") H tmp_7;
    @name("tmp_5") bit<8> tmp_8;
    state start {
        {
            bit<3> val_0 = 3w1;
            bit<3> bound_0 = 3w2;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<3> retval_0;
            @name("tmp") bit<3> tmp_0;
            hasReturned_0 = false;
            if (val_0 < bound_0) {
                tmp_0 = val_0;
            } else {
                tmp_0 = bound_0;
            }
            {
                hasReturned_0 = true;
                retval_0 = tmp_0;
            }
            tmp_1 = retval_0;
        }
        tmp_6 = tmp_1;
        tmp_7 = hdr.h[tmp_6];
        tmp_8 = extern_call(tmp_7);
        hdr.h[tmp_6] = tmp_7;
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

