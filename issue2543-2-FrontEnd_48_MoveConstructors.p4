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

bit<16> produce_val() {
    bool hasReturned = false;
    bit<16> retval;
    {
        hasReturned = true;
        retval = 16w9;
    }
    return retval;
}
Headers produce_hdr() {
    bool hasReturned_0 = false;
    Headers retval_0;
    ethernet_t tmp;
    bit<48> tmp_0;
    bit<48> tmp_1;
    bit<16> tmp_2;
    bit<16> tmp_3;
    tmp_0 = 48w1;
    tmp_1 = 48w1;
    tmp_3 = produce_val();
    tmp_2 = tmp_3;
    tmp = (ethernet_t){dst_addr = tmp_0,src_addr = tmp_1,eth_type = tmp_2};
    {
        hasReturned_0 = true;
        retval_0 = (Headers){eth_hdr = tmp};
    }
    return retval_0;
}
control ingress(inout Headers h) {
    apply {
        h = produce_hdr();
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

