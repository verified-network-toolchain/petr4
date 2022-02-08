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

parser P<H>(packet_in pkt, out H hdr);
control C();
package S<H>(P<H> p, C c);
header data_h {
    bit<32> da;
}

struct headers_t {
    data_h data;
}

parser MyP1(packet_in pkt, out headers_t hdr) {
    state start {
        hdr.data.setInvalid();
        transition MyP2_start;
    }
    state MyP2_start {
        transition reject;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control MyC1() {
    apply {
    }
}

S<headers_t>(MyP1(), MyC1()) main;

