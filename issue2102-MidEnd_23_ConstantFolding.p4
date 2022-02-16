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
    bit<1> a;
}

struct headers {
    H h;
}

control c(inout headers hdr) {
    H tmp_h;
    apply {
        if (hdr.h.a < 1w1) {
            {
                tmp_h = hdr.h;
            }
            {
                hdr.h = tmp_h;
            }
        }
    }
}

control e<T>(inout T t);
package top<T>(e<T> e);
top<headers>(c()) main;

