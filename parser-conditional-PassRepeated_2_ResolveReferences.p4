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

parser p(out bit<32> b) {
    bit<32> a = 32w1;
    state start {
        b = (a == 32w0 ? 32w2 : 32w3);
        b = b + 32w1;
        b = (a > 32w0 ? (a > 32w1 ? b + 32w1 : b + 32w2) : b + 32w3);
        transition accept;
    }
}

parser proto(out bit<32> b);
package top(proto _p);
top(p()) main;

