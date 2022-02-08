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
    bit<8> a;
}

header padding {
    bit<8> p;
}

struct headers {
    H       nop;
    padding p;
}

parser p(packet_in packet, out headers hdr) {
    @name("tmp") headers tmp;
    @name("tmp_0") padding tmp_0;
    state start {
        tmp.nop.setInvalid();
        tmp.p.setInvalid();
        tmp_0.setInvalid();
        transition sub_parser_start;
    }
    state sub_parser_start {
        transition sub_parser_next;
    }
    state sub_parser_next {
        transition select(tmp_0.p) {
            8w0: sub_parser_parse_hdr;
            default: start_0;
        }
    }
    state sub_parser_parse_hdr {
        packet.extract<H>(tmp.nop);
        transition sub_parser_next;
    }
    state start_0 {
        hdr = tmp;
        hdr.p = tmp_0;
        transition accept;
    }
}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;

