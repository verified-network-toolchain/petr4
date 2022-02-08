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

control E(out bit<1> b);
control Ingress(out bit<1> b) {
    apply {
        {
            {
                b = 1w1;
            }
        }
        {
            {
                b = 1w0;
            }
        }
    }
}

package top(E _e);
top(Ingress()) main;

