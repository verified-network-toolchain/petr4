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

parser simple(out bit<1> z);
package m(simple n);
parser p1_0(out bit<1> z1) {
    state start {
        z1 = 1w0;
        transition accept;
    }
}

parser p_0(out bit<1> z) {
    state start {
        transition p1_0_start;
    }
    state p1_0_start {
        z = 1w0;
        transition start_0;
    }
    state start_0 {
        z = z & 1w0 & 1w1;
        transition accept;
    }
}

m(p_0()) main;

