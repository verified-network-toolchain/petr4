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
        standard_metadata.egress_spec = 9w0b101010011;
    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

    action set_one () {
        standard_metadata.egress_spec = 1;
    }

    action set_two () {
        standard_metadata.egress_spec = 2;
    }

    action set_three () {
        standard_metadata.egress_spec = 3;
    }

    action set_four () {
        standard_metadata.egress_spec = 4;
    }


    table my_table {
        key = { standard_metadata.egress_spec : lpm;}
        actions = { set_one; set_two; }
        const entries = {
            9w0b101010101 &&& 9w0b000000000 : set_one;
            9w0b101010101 &&& 9w0b111111100 : set_three;
            9w0b101010101 &&& 9w0b111110000 : set_two;
            9w0b101010101 &&& 9w0b111111111 : set_four;
            }
    }

    apply {
        my_table.apply();
        exit;
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
