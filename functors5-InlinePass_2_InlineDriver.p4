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

parser simple(out bit<2> w);
package m(simple n);
parser p1_0(out bit<2> w) {
    state start {
        w = 2w2;
        transition accept;
    }
}

parser p2_0(out bit<2> w) {
    @name("x") p1_0() x_0;
    state start {
        transition p1_0_start;
    }
    state p1_0_start {
        w = 2w2;
        transition start_0;
    }
    state start_0 {
        transition accept;
    }
}

m(p2_0()) main;

