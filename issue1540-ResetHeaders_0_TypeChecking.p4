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

control Ingress<H, M>(inout H h, inout M m);
control IngressDeparser<H>(packet_out pkt, inout H h);
package Pipeline<H, M>(Ingress<H, M> g, IngressDeparser<H> _c);
package Top<H1, M1, H2, M2>(Pipeline<H1, M1> p0, Pipeline<H2, M2> p1);
header header_t {
}

struct metadata_t {
}

control IngressMirror() {
    apply {
    }
}

control SwitchIngress(inout header_t t, inout metadata_t m) {
    apply {
    }
}

control SwitchIngressDeparser(packet_out pkt, inout header_t h) {
    IngressMirror() im;
    apply {
        im.apply();
    }
}

Pipeline<header_t, metadata_t>(SwitchIngress(), SwitchIngressDeparser()) p0;

Pipeline<header_t, metadata_t>(SwitchIngress(), SwitchIngressDeparser()) p1;

Top<header_t, metadata_t, header_t, metadata_t>(p0, p1) main;

