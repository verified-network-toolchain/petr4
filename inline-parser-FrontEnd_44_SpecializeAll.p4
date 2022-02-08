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

parser p0(packet_in p, out Header h) {
    state start {
        p.extract<Header>(h);
        transition accept;
    }
}

parser p1(packet_in p, out Header[2] h) {
    @name("p0inst") p0() p0inst_0;
    state start {
        p0inst_0.apply(p, h[0]);
        p0inst_0.apply(p, h[1]);
        transition accept;
    }
}

parser proto(packet_in p, out Header[2] h);
package top(proto _p);
top(p1()) main;

