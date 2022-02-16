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
    bit<32> b;
}

parser p(packet_in packet, out H h) {
    state start {
        packet.extract<H>(h);
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

parser proto<T>(packet_in p, out T t);
package top<T>(proto<T> p);
top<H>(p()) main;

