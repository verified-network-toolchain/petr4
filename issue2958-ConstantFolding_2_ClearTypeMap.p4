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

header ethernet_t {
    bit<48> dst_addr;
}

struct G {
    ethernet_t eth;
}

struct H {
    G g;
}

struct Headers {
    ethernet_t eth_hdr;
}

control ingress(inout Headers h) {
    @name("tmp") H tmp_0;
    apply {
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

