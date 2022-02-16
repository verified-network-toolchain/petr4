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

control Wrapped(inout bit<8> valueSet) {
    @name("set") action set(bit<8> value) {
        valueSet = value;
    }
    @name("doSet") table doSet {
        actions = {
            set();
        }
        default_action = set(8w0);
    }
    apply {
        doSet.apply();
    }
}

control Wrapper(inout bit<8> value) {
    Wrapped() wrapped;
    apply {
        wrapped.apply(value);
    }
}

control c(inout bit<8> v);
package top(c _c);
top(Wrapper()) main;

