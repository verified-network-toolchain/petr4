#include <core.p4>
#include <v1model.p4>

header head {
    bit<8> v;
}

struct metadata { }

parser MyParser(packet_in packet,
                out head[13] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr[15]);
        transition select(packet.lookahead< bit<8> >()) {
            42 : next;
            _ : reject;
        }
    }

    state next {
        hdr.push_front(1);
        packet.extract(hdr[0]);
        transition select(packet.lookahead< bit<8> >()) {
            _ : next;
        }
    }

    state final {
        hdr.push_front(1);
        packet.extract(hdr[0]);
        transition accept;
    }

}

control MyChecksum(inout head[13] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout head[13] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply { }
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
