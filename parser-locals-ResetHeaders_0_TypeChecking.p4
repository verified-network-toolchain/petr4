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

header H {
    bit<32> a;
    bit<32> b;
}

struct S {
    H       h1;
    H       h2;
    bit<32> c;
}

parser p() {
    state start {
        S s;
        s.c = 32w0;
        transition accept;
    }
}

parser empty();
package top(empty e);
top(p()) main;

