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

bit<8> test(inout bit<8> x) {
    bool hasReturned = false;
    bit<8> retval;
    {
        hasReturned = true;
        retval = x;
    }
    return retval;
}
control c(inout bit<8> a) {
    apply {
        test(a);
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

