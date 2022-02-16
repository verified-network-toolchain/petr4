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

control c(inout bit<8> a) {
    @name("x_0") bit<8> x;
    @name("hasReturned") bool hasReturned;
    @name("retval") bit<8> retval;
    apply {
        {
            x = a;
            hasReturned = false;
            hasReturned = true;
            retval = x;
            a = x;
        }
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

