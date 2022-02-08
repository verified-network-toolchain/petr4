header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

control c(inout Headers hdr) {
    @name("tmp_val") bit<16> tmp_val;
    @name("do_action") action do_action_0() {
        hdr.eth_hdr.eth_type = 16w3 + (tmp_val > 16w2 ? 16w3 : 16w1);
    }
    @name("do_action") action do_action_2() {
        hdr.eth_hdr.eth_type = 16w3 + (tmp_val > 16w2 ? 16w3 : 16w1);
    }
    apply {
        tmp_val = 16w3;
        do_action_0();
        tmp_val = 16w1;
        do_action_2();
    }
}

control proto(inout Headers hdr);
package top(proto _p);
top(c()) main;

