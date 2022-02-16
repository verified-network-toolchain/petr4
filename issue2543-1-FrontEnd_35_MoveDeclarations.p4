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
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

bit<16> give_val() {
    return 16w1;
}
ethernet_t give_hdr() {
    @name("dummy") bit<16> dummy_0;
    return (ethernet_t){dst_addr = 48w1,src_addr = 48w1,eth_type = 16w1};
    dummy_0 = 16w1;
    return (ethernet_t){dst_addr = 48w1,src_addr = 48w1,eth_type = dummy_0};
}
control ingress(inout Headers h) {
    @name("foo") Headers foo_0 = (Headers){eth_hdr = (ethernet_t){dst_addr = 48w1,src_addr = 48w1,eth_type = give_val()}};
    apply {
        give_hdr();
        foo_0.eth_hdr.eth_type[3:0] = 4w1;
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

