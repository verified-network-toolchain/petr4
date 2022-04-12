
#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers {
    bool i;
 }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr);
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
        
    }
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
V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
