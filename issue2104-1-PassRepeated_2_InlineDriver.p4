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
    @name("hasReturned") bool hasReturned_0;
    @name("retval") bit<8> retval_0;
    hasReturned_0 = false;
    {
        hasReturned_0 = true;
        retval_0 = x;
    }
    return retval_0;
}
control c(inout bit<8> a) {
    apply {
        {
            bit<8> x_0 = a;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            {
                hasReturned_0 = true;
                retval_0 = x_0;
            }
            a = x_0;
        }
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

