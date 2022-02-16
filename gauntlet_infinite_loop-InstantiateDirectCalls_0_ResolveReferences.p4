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
    bit<8> a;
}

header padding {
    bit<8> p;
}

struct headers {
    H       nop;
    padding p;
}

parser sub_parser(packet_in b, out headers hdr, out padding padding) {
    state start {
        transition next;
    }
    state next {
        transition select(padding.p) {
            0: parse_hdr;
            default: accept;
        }
    }
    state parse_hdr {
        b.extract(hdr.nop);
        transition next;
    }
}

parser p(packet_in packet, out headers hdr) {
    state start {
        sub_parser.apply(packet, hdr, hdr.p);
        transition accept;
    }
}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;

