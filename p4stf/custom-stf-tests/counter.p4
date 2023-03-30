#include <core.p4>
#include <v1model.p4>

const bit<32> ctr_size = 128;

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
    counter(ctr_size, CounterType.packets) pkt_ctr;
    counter(ctr_size, CounterType.bytes) byt_ctr;
    counter(ctr_size, CounterType.packets_and_bytes) both_ctr;
    bit<32> index;
    apply {
        index = 2;
        pkt_ctr.count(index);
        byt_ctr.count(index);
        both_ctr.count(index);
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
