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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

header Header {
    bit<32> data;
    bit<32> data2;
}

parser p0(packet_in p, out Header h) {
    state start {
        p.extract<Header>(h);
        h.data = h.data2 - 32w8 - 32w8 - 32w2 - 32w16;
        transition accept;
    }
}

parser proto(packet_in p, out Header h);
package top(proto _p);
top(p0()) main;

