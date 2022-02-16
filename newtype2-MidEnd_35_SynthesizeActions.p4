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

typedef bit<9> PortIdUInt_t;
typedef bit<9> PortId_t;
struct M {
    PortId_t     e;
    PortIdUInt_t es;
}

control Ingress(inout M sm);
package V1Switch(Ingress ig);
control FabricIngress(inout M sm) {
    @hidden action newtype2l16() {
        sm.es = (PortIdUInt_t)sm.e;
    }
    apply {
        newtype2l16();
    }
}

V1Switch(FabricIngress()) main;

