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

control HwControl<H>(inout H hdr);
package Switch<H>(HwControl<H> c);
extern void HwSplFunc<T, R>(in T hdr1, @optional in R hdr2);
header eth_t {
    bit<48> sa;
    bit<48> da;
    bit<16> type;
}

struct parsed_header_t {
    eth_t mac;
}

control match_action_unit(inout parsed_header_t hdr) {
    apply {
        HwSplFunc(hdr.mac);
    }
}

Switch(match_action_unit()) main;

