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
        ;
        h.data[7:0] = 8w8;
        transition select(h.data[15:8]) {
            8w0: next;
            default: next2;
        }
    }
    state next {
        ;
        h.data = 32w8;
        transition final;
    }
    state next2 {
        h.data[7:2] = 6w9;
        ;
        h.data[7:2] = 6w3;
        transition final;
    }
    state final {
        ;
        ;
        h.data[15:8] = 8w6;
        transition accept;
    }
}

parser proto(packet_in p, out Header h);
package top(proto _p);
top(p0()) main;

