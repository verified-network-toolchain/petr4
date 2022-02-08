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
    @name("sub_parser.tracker") bit<8> sub_parser_tracker;
    state start {
        hdr.nop.setInvalid();
        hdr.p.setInvalid();
        transition sub_parser_start;
    }
    state sub_parser_start {
        sub_parser_tracker = 8w0;
        transition sub_parser_next;
    }
    state sub_parser_next {
        transition select(sub_parser_tracker == 8w1) {
            true: sub_parser_next_true;
            false: sub_parser_next_join;
        }
    }
    state sub_parser_next_true {
        packet.extract<padding>(hdr.p);
        hdr.p.p = 8w1;
        transition sub_parser_next_join;
    }
    state sub_parser_next_join {
        transition select(hdr.p.p) {
            8w0: sub_parser_parse_hdr;
            default: start_0;
        }
    }
    state sub_parser_parse_hdr {
        sub_parser_tracker = sub_parser_tracker + 8w1;
        packet.extract<H>(hdr.nop);
        transition sub_parser_next;
    }
    state start_0 {
        transition accept;
    }
}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;

