
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
    apply {
        //hdr.i = true;
        //headers h;
        //h.i = true;
        //hdr = h;
        //standard_metadata.egress_spec = 9w9;
        mark_to_drop(standard_metadata);
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { 
        //hdr.i = true;
        
        //standard_metadata.egress_port = 9w9;
        }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

//this is declaration
V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
