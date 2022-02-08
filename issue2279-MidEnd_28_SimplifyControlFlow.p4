header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

control c(inout Headers hdr) {
    @name("c.do_action") action do_action() {
        hdr.eth_hdr.eth_type = 16w6;
    }
    @name("c.do_action") action do_action_1() {
        hdr.eth_hdr.eth_type = 16w6;
    }
    apply {
        do_action();
        do_action_1();
    }
}

control proto(inout Headers hdr);
package top(proto _p);
top(c()) main;

