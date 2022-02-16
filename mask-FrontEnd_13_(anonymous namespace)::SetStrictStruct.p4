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

header IPv4_option_NOP {
    bit<8> value;
}

struct Parsed_Packet {
    IPv4_option_NOP[3] nop;
}

parser Parser(packet_in b, out Parsed_Packet p) {
    state start {
        transition select(8w0, b.lookahead<bit<8>>()) {
            default: accept;
            (8w0, 8w0 &&& 8w0): accept;
            (8w0 &&& 8w0, 8w0x44): ipv4_option_NOP;
        }
    }
    state ipv4_option_NOP {
        b.extract(p.nop.next);
        transition start;
    }
}

package Switch();
Switch() main;

