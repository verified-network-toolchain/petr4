#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers {
    bit<9> first;
    bit<9> second;
    bit<9> third;
    bit<9> fourth;
    bit<9> fifth;
}

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
        headers.first = 1;
        transition select(8w0x7A) {
            b &&& 8w0x1A : accept;
            a &&& b : second_state;
            _ : accept;
        }
    }

    state second_state {
        headers.second = 2;
        transition select(8w0xDC) {
            b &&& c : accept;
            _ : third_state;
        }
    }

    state third_state {
        headers.third = 3;
        transition select(8w0xA5) {
            b &&& c : fourth_state;
            default : accept;
        }
    }

    state fourth_state {
        headers.fourth = 4;
        transition select(8w0x7A, 8w0xA5) {
            (a &&& b, a &&& b) : accept;
            (b &&& c, b &&& c) : accept;
            (b &&& c, a &&& b) : accept;
            (a &&& b, b &&& c) : fifth_state;
            _ : accept;
        }
    }

    state fifth_state {
        headers.fifth = 5;
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
    apply {
        packet.emit(headers.first);
        packet.emit(headers.second);
        packet.emit(headers.third);
        packet.emit(headers.fourth);
        packet.emit(headers.fifth);
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
