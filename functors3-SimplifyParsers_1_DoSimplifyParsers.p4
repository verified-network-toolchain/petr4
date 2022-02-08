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

parser p1(out bit<1> z1)(bit<1> b1) {
    state start {
        z1 = b1;
        transition accept;
    }
}

parser p(out bit<1> z)(bit<1> b, bit<1> c) {
    p1(b) p1i;
    state start {
        p1i.apply(z);
        z = z & b & c;
        transition accept;
    }
}

parser simple(out bit<1> z);
package m(simple n);
m(p(1w0, 1w1)) main;

