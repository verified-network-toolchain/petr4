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

typedef bit<4> PortId;
struct InControl {
    PortId inputPort;
}

struct OutControl {
    PortId outputPort;
}

parser Parser<IH>(packet_in b, out IH parsedHeaders);
control IPipe<T, IH, OH>(in IH inputHeaders, in InControl inCtrl, out OH outputHeaders, out T toEgress, out OutControl outCtrl);
control EPipe<T, IH, OH>(in IH inputHeaders, in InControl inCtrl, in T fromIngress, out OH outputHeaders, out OutControl outCtrl);
control Deparser<OH>(in OH outputHeaders, packet_out b);
package Ingress<T, IH, OH>(Parser<IH> p, IPipe<T, IH, OH> map, Deparser<OH> d);
package Egress<T, IH, OH>(Parser<IH> p, EPipe<T, IH, OH> map, Deparser<OH> d);
package Switch<T>(Ingress<T, _, _> ingress, Egress<T, _, _> egress);
