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

control ingress(inout Headers h) {
    @name("hasReturned_0") bool hasReturned;
    @name("retval_0") Headers retval;
    @name("tmp") ethernet_t tmp;
    @name("tmp_0") bit<48> tmp_0;
    @name("tmp_1") bit<48> tmp_1;
    @name("tmp_2") bit<16> tmp_2;
    @name("tmp_3") bit<16> tmp_3;
    @name("hasReturned") bool hasReturned_0;
    @name("retval") bit<16> retval_0;
    apply {
        {
            hasReturned = false;
            tmp_0 = 48w1;
            tmp_1 = 48w1;
            {
                hasReturned_0 = false;
                hasReturned_0 = true;
                retval_0 = 16w9;
                tmp_3 = retval_0;
            }
            tmp_2 = tmp_3;
            tmp.setValid();
            tmp = (ethernet_t){dst_addr = tmp_0,src_addr = tmp_1,eth_type = tmp_2};
            hasReturned = true;
            retval = (Headers){eth_hdr = tmp};
            h = retval;
        }
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

