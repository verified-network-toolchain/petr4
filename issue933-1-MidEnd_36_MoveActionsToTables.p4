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

struct headers {
    bit<32> x;
}

extern void f(headers h);
control c() {
    @hidden action issue9331l13() {
        f((headers){x = 32w5});
    }
    @hidden table tbl_issue9331l13 {
        actions = {
            issue9331l13();
        }
        const default_action = issue9331l13();
    }
    apply {
        tbl_issue9331l13.apply();
    }
}

control C();
package top(C _c);
top(c()) main;

