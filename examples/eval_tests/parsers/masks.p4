#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    bit<8> a = 8w0x0A;
    bit<8> b = 8w0x0F;
    bit<8> c = 8w0x55;

    state start {
        transition select(8w0x0A) {
            a &&& b : first_state;
            _ : accept;
        }
    }

    state first_state {
        standard_metadata.egress_spec = 1;
        transition select(8w0x7A) {
            b &&& 8w0x1A : accept;
            a &&& b : second_state;
            _ : accept;
        }
    }

    state second_state {
        standard_metadata.egress_spec = 2;
        transition select(8w0xDC) {
            b &&& c : accept;
            _ : third_state;
        }
    }

    state third_state {
        standard_metadata.egress_spec = 3;
        transition select(8w0xA5) {
            b &&& c : fourth_state;
            default : accept;
        }
    }

    state fourth_state {
        standard_metadata.egress_spec = 4;
        transition select(8w0x7A, 8w0xA5) {
            (a &&& b, a &&& b) : accept;
            (b &&& c, b &&& c) : accept;
            (b &&& c, a &&& b) : accept;
            (a &&& b, b &&& c) : fifth_state;
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
