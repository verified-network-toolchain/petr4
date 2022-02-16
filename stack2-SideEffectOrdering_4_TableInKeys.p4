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

header h {
}

control c(out bit<32> x) {
    @name("sz") bit<32> sz_0;
    apply {
        sz_0 = 32w4;
        x = sz_0;
    }
}

control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;

