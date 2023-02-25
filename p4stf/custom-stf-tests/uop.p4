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
        bit<8> a = (bit<8>) ~4w5; // 10
        bit<8> b = (bit<8>) -4w5; // 11
        // works
        bit<8> c = (bit<8>) -8s5; // -5
        // does not work
        //bit<8> c = (bit<8>) -4s5; // -5
        bit<8> d = (bit<8>) -4 + 5; //1
        packet.emit(a);
        packet.emit(b);
        packet.emit(c);
        packet.emit(d);
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
    ) main;
