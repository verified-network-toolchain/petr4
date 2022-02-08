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

parser Parser<IH>(out IH parsedHeaders);
package Ingress<IH>(Parser<IH> p);
package Switch<IH>(Ingress<IH> ingress);
struct H {
}

parser ing_parse(out H hdr) {
    state start {
        transition accept;
    }
}

Ingress<H>(ing_parse()) ig1;

Switch<H>(ig1) main;

