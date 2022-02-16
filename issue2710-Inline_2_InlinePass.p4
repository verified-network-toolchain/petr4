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

control Wrapper(inout bit<8> value) {
    @name("wrapped.set") action wrapped_set(@name("value") bit<8> value_0) {
        value = value_0;
    }
    @name("wrapped.doSet") table wrapped_doSet {
        actions = {
            wrapped_set();
        }
        default_action = wrapped_set(8w0);
    }
    apply {
        {
            wrapped_doSet.apply();
        }
    }
}

control c(inout bit<8> v);
package top(c _c);
top(Wrapper()) main;

