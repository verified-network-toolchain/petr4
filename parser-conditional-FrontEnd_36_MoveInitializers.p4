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
    @name("a") bit<32> a_0;
    state start {
        a_0 = 32w1;
        transition start_0;
    }
    state start_0 {
        b = (a_0 == 32w0 ? 32w2 : 32w3);
        b = b + 32w1;
        b = (a_0 > 32w0 ? (a_0 > 32w1 ? b + 32w1 : b + 32w2) : b + 32w3);
        transition accept;
    }
}

parser proto(out bit<32> b);
package top(proto _p);
top(p()) main;

