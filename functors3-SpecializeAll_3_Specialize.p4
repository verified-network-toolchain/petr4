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
    @name("p1i") p1(b) p1i_0;
    state start {
        p1i_0.apply(z);
        z = z & b & c;
        transition accept;
    }
}

parser simple(out bit<1> z);
package m(simple n);
parser p_0(out bit<1> z) {
    @name("p1i") p1(1w0) p1i_0;
    state start {
        p1i_0.apply(z);
        z = z & 1w0 & 1w1;
        transition accept;
    }
}

m(p_0()) main;

