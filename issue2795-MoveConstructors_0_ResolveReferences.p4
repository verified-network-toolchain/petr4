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

control c(packet_out p) {
    H tmp;
    H tmp_0;
    apply {
        tmp = (H){a = 32w0,b = 32w1};
        p.emit<H>(tmp);
        tmp_0 = (H){a = 32w0,b = 32w1};
        p.emit<H>(tmp_0);
    }
}

control ctr(packet_out p);
package top(ctr _c);
top(c()) main;

