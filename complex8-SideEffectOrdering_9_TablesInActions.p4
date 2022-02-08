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

extern bit<32> f(in bit<32> x);
parser p() {
    bit<32> tmp;
    bit<32> tmp_0;
    state start {
        tmp_0 = f(32w2);
        tmp = tmp_0;
        transition select(tmp) {
            32w0: accept;
            default: reject;
        }
    }
}

parser simple();
package top(simple e);
top(p()) main;

