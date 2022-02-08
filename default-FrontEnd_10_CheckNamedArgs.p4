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
}

parser p0(packet_in p, out Header h) {
    bool b = true;
    state start {
        p.extract(h);
        transition select(h.data, b) {
            (default, true): next;
            (default, default): reject;
        }
    }
    state next {
        p.extract(h);
        transition select(h.data, b) {
            (default, true): accept;
            (default, default): reject;
            default: reject;
        }
    }
}

parser proto(packet_in p, out Header h);
package top(proto _p);
top(p0()) main;

