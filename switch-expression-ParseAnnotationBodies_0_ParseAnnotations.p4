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

control c(inout bit<32> b) {
    apply {
        switch (b) {
            16: 
            32: {
                b = 1;
            }
            64: {
                b = 2;
            }
            92: 
            default: {
                b = 3;
            }
        }
    }
}

control ct(inout bit<32> b);
package top(ct _c);
top(c()) main;

