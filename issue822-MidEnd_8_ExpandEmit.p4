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

control C();
package S(C c);
extern BoolRegister {
    BoolRegister();
}

extern ActionSelector {
    ActionSelector(BoolRegister reg);
}

BoolRegister() r;

control MyC1() {
    @name("MyC1.action_selector") ActionSelector(r) action_selector_0;
    apply {
    }
}

S(MyC1()) main;

