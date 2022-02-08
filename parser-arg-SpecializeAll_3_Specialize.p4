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

parser Parser();
package Package(Parser p1, Parser p2);
parser Parser1()(Parser p) {
    state start {
        p.apply();
        transition accept;
    }
}

parser Parser2()(Parser p) {
    state start {
        p.apply();
        transition accept;
    }
}

parser Inside() {
    state start {
        transition accept;
    }
}

parser Parser1_0() {
    Inside() p_0;
    state start {
        p_0.apply();
        transition accept;
    }
}

parser Parser2_0() {
    Inside() p_1;
    state start {
        p_1.apply();
        transition accept;
    }
}

Package(Parser1_0(), Parser2_0()) main;

