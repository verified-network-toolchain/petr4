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

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
}

struct Headers {
    ethernet_t eth_hdr;
}

control ingress(inout Headers h) {
    apply {
        h.eth_hdr = (h.eth_hdr.eth_type == 16w1 ? (ethernet_t){dst_addr = 48w1,src_addr = 48w1,eth_type = 16w1} : (ethernet_t){dst_addr = 48w2,src_addr = 48w2,eth_type = 16w2});
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

