#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    bit<8> a = 8w7;
    bit<8> b = 8w6;

    state start {
        transition select(a) {
            7 : first_state;
            _ : accept;
        }
    }

    state first_state {
        standard_metadata.egress_spec = 1;
        transition select(b) {
            6 : second_state;
            _ : accept;
        }
    }

    state second_state {
        standard_metadata.egress_spec = 2;
        transition select(a) {
            0 : accept;
            _ : third_state;
        }
    }

    state third_state {
        standard_metadata.egress_spec = 3;
        transition select(a) {
            0 : accept;
            default : fourth_state;
        }
    }

    state fourth_state {
        standard_metadata.egress_spec = 4;
        transition select(a,b) {
            (6,7) : accept;
            (0,0) : accept;
            (_,2) : accept;
            (7,6) : fifth_state;
            _ : accept;
        }
    }

    state fifth_state {
        standard_metadata.egress_spec = 5;
        transition accept;
    }
    // egress spec should be 0, 1, 2, 3, 4, then 5 in that order
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

//this is declaration
V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
