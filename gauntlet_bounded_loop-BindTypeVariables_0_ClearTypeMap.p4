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

parser sub_parser(packet_in b, out headers hdr) {
    bit<8> tracker;
    state start {
        tracker = (bit<8>)8w0;
        transition next;
    }
    state next {
        if (tracker == 8w1) {
            b.extract(hdr.p);
            hdr.p.p = (bit<8>)8w1;
        }
        transition select(hdr.p.p) {
            8w0: parse_hdr;
            default: accept;
        }
    }
    state parse_hdr {
        tracker = tracker + 8w1;
        b.extract(hdr.nop);
        transition next;
    }
}

parser p(packet_in packet, out headers hdr) {
    @name("sub_parser") sub_parser() sub_parser_inst;
    state start {
        sub_parser_inst.apply(packet, hdr);
        transition accept;
    }
}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;

