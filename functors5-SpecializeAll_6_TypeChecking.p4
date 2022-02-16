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

parser p1(out bit<2> w)(bit<2> a) {
    state start {
        w = 2w2;
        transition accept;
    }
}

parser simple(out bit<2> w);
package m(simple n);
parser p2_0(out bit<2> w) {
    @name("x") p1(2w1) x_0;
    state start {
        x_0.apply(w);
        transition accept;
    }
}

m(p2_0()) main;

