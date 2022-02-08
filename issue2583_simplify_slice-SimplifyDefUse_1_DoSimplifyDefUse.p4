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

header Header {
    bit<32> data;
}

parser p(packet_in pckt, out Header h) {
    state start {
        h.data = 32w0;
        ;
        h.data = 32w7;
        ;
        ;
        h.data[15:0] = 16w8;
        h.data[31:16] = 16w5;
        transition accept;
    }
}

parser proto(packet_in pckt, out Header h);
package top(proto _p);
top(p()) main;

