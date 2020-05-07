#include <core.p4>
#include <v1model.p4>

header elt {
    bit<8> v;
}

struct metadata { }
struct headers {
    elt first;
    elt second;
    elt third;
    elt fourth;
    elt fifth;
    elt sixth;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    bit<8> a = 8w5;
    bit<8> b = 8w8;

    state start {
        packet.extract(hdr.first);
        transition select(8w5) {
            a..b : first_state;
            _ : accept;
        }
    }

    state first_state {
        packet.extract(hdr.second);
        transition select(8w8) {
            a..b : second_state;
            _ : accept;
        }
    }

    state second_state {
        packet.extract(hdr.third);
        transition select(8w5) {
            a..b : third_state;
            _ : accept;
        }
    }

    state third_state {
        packet.extract(hdr.fourth);
        transition select(8w0) {
            a..b : accept;
            default : fourth_state;
        }
    }

    state fourth_state {
        packet.extract(hdr.fifth);
        transition select(8w7, 8w42) {
            (8w8..8w12,8w40..8w44) : accept;
            (8w6..8w9,8w38..8w40) : accept;
            (8w40..8w44,8w6..8w9) : accept;
            (8w6..8w9,8w40..8w44) : fifth_state;
            _ : accept;
        }
    }

    state fifth_state {
        packet.extract(hdr.sixth);
        transition accept;
    }
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
    apply {
        packet.emit(hdr);
    }
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
