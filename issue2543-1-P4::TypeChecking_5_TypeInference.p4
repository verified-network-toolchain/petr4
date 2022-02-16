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
    ;
    return (ethernet_t){dst_addr = 48w1,src_addr = 48w1,eth_type = dummy_0};
}
control ingress(inout Headers h) {
    @name("foo") Headers foo_0;
    ethernet_t tmp;
    bit<48> tmp_0;
    bit<48> tmp_1;
    bit<16> tmp_2;
    bit<16> tmp_3;
    apply {
        tmp_0 = 48w1;
        tmp_1 = 48w1;
        tmp_3 = give_val();
        tmp_2 = tmp_3;
        tmp = (ethernet_t){dst_addr = tmp_0,src_addr = tmp_1,eth_type = tmp_2};
        ;
        ;
        ;
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

