#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
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
        bit<8> a = (8w0b00101010 << 6) >> 7; //1
        bit<8> b = (8w0b00101010 << 2); //168
        bit<8> c = 8w168 >> 2; //42
        int<8> d = (8s42 << 6) >> 7; //-1
        int<8> e = 8s42 << 2; //-88
        int<8> f = (8s42 << 2) >> 2; //-22
        packet.emit(a);
        packet.emit(b);
        packet.emit(c);
        // packet.emit(d);
        // packet.emit(e);
        // packet.emit(f);
    }
}

// @rhd TODO this exposes a bug in the type checker

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    ) main;
