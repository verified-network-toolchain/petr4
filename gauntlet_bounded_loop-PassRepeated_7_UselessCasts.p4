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
    @name("tracker") bit<8> tracker_0;
    state start {
        tracker_0 = 8w0;
        transition next;
    }
    state next {
        transition select(tracker_0 == 8w1) {
            true: next_true;
            false: next_join;
        }
    }
    state next_true {
        b.extract<padding>(hdr.p);
        hdr.p.p = 8w1;
        transition next_join;
    }
    state next_join {
        transition select(hdr.p.p) {
            8w0: parse_hdr;
            default: accept;
        }
    }
    state parse_hdr {
        tracker_0 = tracker_0 + 8w1;
        b.extract<H>(hdr.nop);
        transition next;
    }
}

parser p(packet_in packet, out headers hdr) {
    @name("sub_parser") sub_parser() sub_parser_inst_0;
    state start {
        sub_parser_inst_0.apply(packet, hdr);
        transition accept;
    }
}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;

