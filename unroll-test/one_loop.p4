
#include <core.p4>
#include <v1model.p4>

header byte_t {
    bit<8> byte;
}

struct metadata { }
struct headers {
    byte_t h;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition loop_hdr;
    }

    state loop_hdr {
        packet.lookahead<headers>();
        transition select(hdr.h.byte) {
            8w0 : continue;
            default : break;
        }
    }

    state continue {
        hdr.h.setInvalid();
        packet.advance(8w8);
        transition loop_hdr;
    }

    state break {
        hdr.h.setInvalid();
        packet.extract(hdr);
        transition select(hdr.h.byte) {
            8w0 : loop_hdr;
            default : accept;
        }
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        standard_metadata.egress_spec = 9;
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

//this is declaration
V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
