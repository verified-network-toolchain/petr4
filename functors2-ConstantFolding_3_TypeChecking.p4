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

parser p1(out bit<2> z1)(bit<2> a) {
    state start {
        z1 = a;
        transition accept;
    }
}

parser simple(out bit<2> z);
package m(simple n);
parser p2_0(out bit<2> z2) {
    @name("x1") bit<2> x1_0;
    @name("x2") bit<2> x2_0;
    @name("x3") bit<2> x3_0;
    @name("p1a") p1(2w0) p1a_0;
    @name("p1b") p1(2w1) p1b_0;
    @name("p1c") p1(2w2) p1c_0;
    state start {
        p1a_0.apply(x1_0);
        p1b_0.apply(x2_0);
        p1c_0.apply(x3_0);
        z2 = 2w1 | 2w2 | x1_0 | x2_0 | x3_0;
        transition accept;
    }
}

m(p2_0()) main;

