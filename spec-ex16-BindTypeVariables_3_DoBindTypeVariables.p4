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

parser Prs<T>(packet_in b, out T result);
control Map<T>(in T d);
package Switch<T>(Prs<T> prs, Map<T> map);
parser P(packet_in b, out bit<32> d) {
    state start {
        transition accept;
    }
}

control Map1(in bit<32> d) {
    apply {
    }
}

control Map2(in bit<8> d) {
    apply {
    }
}

Switch<bit<32>>(P(), Map1()) main;

Switch<bit<32>>(P(), Map1()) main1;

