#include <core.p4>
#include <v1model.p4>

header head {
    bit<8> v;
}

struct metadata { }

parser MyParser(packet_in packet,
                out head[13] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }

}

control MyChecksum(inout head[13] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout head[13] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        standard_metadata.egress_port = 1;
    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

    action set_zero() {
        standard_metadata.egress_spec = 0;
    }

    action set_one () {
        standard_metadata.egress_spec = 1;
    }
    
    action set_two () {
        standard_metadata.egress_spec = 2;
    }

    action set_three () {
        standard_metadata.egress_spec = 3;
    }

    table my_table {
        key = { standard_metadata.egress_port : exact;}
        actions = { set_zero; set_one; set_two; set_three; }
        const entries = {
            0 : set_three;
            1 : set_two;
            2 : set_one;
            3 : set_zero;
        }
    }

    apply {
        switch (my_table.apply().action_run) {
            default : { standard_metadata.ingress_port = 0; }
            set_one : { standard_metadata.ingress_port = 1; }
            set_two : { standard_metadata.ingress_port = 2; }
            set_three : { standard_metadata.ingress_port = 3; }
        }
    }

}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr);
    }
}

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
