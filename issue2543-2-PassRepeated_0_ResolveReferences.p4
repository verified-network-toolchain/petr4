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
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<16> retval_1;
    hasReturned_1 = false;
    {
        hasReturned_1 = true;
        retval_1 = 16w9;
    }
    return retval_1;
}
Headers produce_hdr() {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") Headers retval_2;
    @name("tmp") ethernet_t tmp_4;
    @name("tmp_0") bit<48> tmp_5;
    @name("tmp_1") bit<48> tmp_6;
    @name("tmp_2") bit<16> tmp_7;
    @name("tmp_3") bit<16> tmp_8;
    hasReturned_2 = false;
    tmp_5 = 48w1;
    tmp_6 = 48w1;
    {
        @name("hasReturned") bool hasReturned_1;
        @name("retval") bit<16> retval_1;
        hasReturned_1 = false;
        {
            hasReturned_1 = true;
            retval_1 = 16w9;
        }
        tmp_8 = retval_1;
    }
    tmp_7 = tmp_8;
    tmp_4 = (ethernet_t){dst_addr = tmp_5,src_addr = tmp_6,eth_type = tmp_7};
    {
        hasReturned_2 = true;
        retval_2 = (Headers){eth_hdr = tmp_4};
    }
    return retval_2;
}
control ingress(inout Headers h) {
    apply {
        {
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") Headers retval_2;
            @name("tmp") ethernet_t tmp_4;
            @name("tmp_0") bit<48> tmp_5;
            @name("tmp_1") bit<48> tmp_6;
            @name("tmp_2") bit<16> tmp_7;
            @name("tmp_3") bit<16> tmp_8;
            hasReturned_2 = false;
            tmp_5 = 48w1;
            tmp_6 = 48w1;
            {
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<16> retval_1;
                hasReturned_1 = false;
                {
                    hasReturned_1 = true;
                    retval_1 = 16w9;
                }
                tmp_8 = retval_1;
            }
            tmp_7 = tmp_8;
            tmp_4 = (ethernet_t){dst_addr = tmp_5,src_addr = tmp_6,eth_type = tmp_7};
            {
                hasReturned_2 = true;
                retval_2 = (Headers){eth_hdr = tmp_4};
            }
            h = retval_2;
        }
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

