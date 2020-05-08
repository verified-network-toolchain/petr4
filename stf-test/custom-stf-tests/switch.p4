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
        hdr[0].v = 0;
        hdr[0].setValid();
    }

    action set_one () {
        hdr[0].v = 1;
        hdr[0].setValid();
    }
    
    action set_two () {
        hdr[0].v = 2;
        hdr[0].setValid();
    }

    action set_three () {
        hdr[0].v = 3;
        hdr[0].setValid();
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
            set_one : { hdr[1].v = 1; }
            set_two : { hdr[1].v = 2; }
            set_three : { hdr[1].v = 3; }
            default : { hdr[1].v = 0; }
        }
    }

}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr[0]);
        packet.emit(hdr[1]);
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
