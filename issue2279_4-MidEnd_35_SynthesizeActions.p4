header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

control c(inout Headers hdr) {
    @name("c.tmp_val") bit<16> tmp_val_0;
    @name("c.do_action") action do_action() {
        hdr.eth_hdr.eth_type = 16w6;
    }
    @name("c.do_action") action do_action_1() {
        hdr.eth_hdr.eth_type = 16w3 + (tmp_val_0 > 16w2 ? 16w3 : 16w1);
    }
    @hidden action issue2279_4l12() {
        tmp_val_0 = 16w3;
    }
    @hidden action issue2279_4l19() {
        tmp_val_0 = (hdr.eth_hdr.eth_type >> 1) + 16w65533;
    }
    apply {
        issue2279_4l12();
        do_action();
        issue2279_4l19();
        do_action_1();
    }
}

control proto(inout Headers hdr);
package top(proto _p);
top(c()) main;

