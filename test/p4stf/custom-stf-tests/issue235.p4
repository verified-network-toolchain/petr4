#include <core.p4>
#include <v1model.p4>

header h_t {
    bit<32> v;
}

struct metadata { }
struct headers {
    h_t[10] h;
}

bit<32> incrAndReturn(inout bit<32> x) {
    x = x + 1;
    return x;
}

void incrHdr(inout h_t x) {
    x.v = x.v + 1;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.h.next);
        packet.extract(hdr.h.next);
        packet.extract(hdr.h.next);
        packet.extract(hdr.h.next);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) { 

    apply {
        bit<32> x = 0;
        incrHdr(hdr.h[incrAndReturn(x)]);
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.h);
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
