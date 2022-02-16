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

header h {
}

control c(out bit<32> x) {
    @hidden action stack2l7() {
        x = 32w4;
    }
    @hidden table tbl_stack2l7 {
        actions = {
            stack2l7();
        }
        const default_action = stack2l7();
    }
    apply {
        tbl_stack2l7.apply();
    }
}

control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;

