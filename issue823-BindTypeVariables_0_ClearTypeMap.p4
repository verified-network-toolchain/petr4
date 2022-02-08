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

parser P<H>(packet_in pkt, out H hdr);
control C();
package S<H>(P<H> p, C c);
header data_h {
    bit<32> da;
}

struct headers_t {
    data_h data;
}

parser MyP2(packet_in pkt, out headers_t hdr) {
    state start {
        transition reject;
    }
}

parser MyP1(packet_in pkt, out headers_t hdr) {
    MyP2() subp;
    state start {
        subp.apply(pkt, hdr);
        transition accept;
    }
}

control MyC1() {
    apply {
    }
}

S(MyP1(), MyC1()) main;

