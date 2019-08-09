#include <core.p4>
#include <v1model.p4>

header head {
    bit<4> a;
    bit<4> b;
    bit<4> c;
    bit<4> d;
}

header head0 {
    bit<4> a;
    bit<4> b;
}

struct metadata { }
struct headers {
    head h1;
    head0 h2;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.h1);
        packet.extract(hdr.h2);
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
        packet.emit(hdr.h1);
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
