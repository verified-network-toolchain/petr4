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

parser p2(out bit<2> z2)(bit<2> b, bit<2> c) {
    p1(2w0) p1a;
    p1(b) p1b;
    p1(c) p1c;
    state start {
        bit<2> x1;
        bit<2> x2;
        bit<2> x3;
        p1a.apply(x1);
        p1b.apply(x2);
        p1c.apply(x3);
        z2 = b | c | x1 | x2 | x3;
        transition accept;
    }
}

parser simple(out bit<2> z);
package m(simple n);
m(p2(2w1, 2w2)) main;

