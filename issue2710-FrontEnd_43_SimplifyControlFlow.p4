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

control Wrapped(inout bit<8> valueSet) {
    @name("set") action set_0(@name("value") bit<8> value_0) {
        valueSet = value_0;
    }
    @name("doSet") table doSet_0 {
        actions = {
            set_0();
        }
        default_action = set_0(8w0);
    }
    apply {
        doSet_0.apply();
    }
}

control Wrapper(inout bit<8> value) {
    @name("wrapped") Wrapped() wrapped_0;
    apply {
        wrapped_0.apply(value);
    }
}

control c(inout bit<8> v);
package top(c _c);
top(Wrapper()) main;

