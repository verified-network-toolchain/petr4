#include <core.p4>
#include <v1model.p4>

header byte_t {
    bit<8> val;
}

struct hdr_t {
    byte_t[1] arr;
}
struct metadata { }

parser MyParser(packet_in packet,
                out hdr_t hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.arr[0]);
        transition accept;
    }
}

control MyChecksum(inout hdr_t hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    apply { }
}

control MyEgress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    apply { }
}

control MyDeparser(packet_out packet, in hdr_t hdr) {
    apply {
        packet.emit(hdr.arr);
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
