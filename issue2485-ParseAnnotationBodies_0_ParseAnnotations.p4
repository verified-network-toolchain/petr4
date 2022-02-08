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

header H {
    bit<16> a;
}

struct metadata {
}

struct Headers {
    H h;
}

parser p(packet_in packet, out Headers hdr) {
    state start {
        packet.extract(hdr.h);
        transition select(hdr.h.a) {
            0x0 .. 0x4: parse;
            default: accept;
        }
    }
    state parse {
        hdr.h.a = 1;
        transition accept;
    }
}

parser Parser(packet_in b, out Headers hdr);
package top(Parser p);
top(p()) main;

