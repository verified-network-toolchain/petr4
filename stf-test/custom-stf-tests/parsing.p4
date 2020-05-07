#include <core.p4>
#include <v1model.p4>

header elt {
  bit<8> v;
}

struct metadata { }
struct headers {
    elt first;
    elt second;
    elt third;
    elt fourth;
    elt fifth;
    elt sixth;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.first);
        transition select(8w7) {
            7 : first_state;
            _ : accept;
        }
    }

    state first_state {
        packet.extract(hdr.second);
        transition select(8w6) {
            6 : second_state;
            _ : accept;
        }
    }

    state second_state {
        packet.extract(hdr.third);
        transition select(8w7) {
            0 : accept;
            _ : third_state;
        }
    }

    state third_state {
        packet.extract(hdr.fourth);
        transition select(8w7) {
            0 : accept;
            default : fourth_state;
        }
    }

    state fourth_state {
        packet.extract(hdr.fifth);
        transition select(8w7,8w6) {
            (6,7) : accept;
            (0,0) : accept;
            (_,2) : accept;
            (7,6) : fifth_state;
            _ : accept;
        }
    }

    state fifth_state {
        packet.extract(hdr.sixth);
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
      packet.emit(hdr);
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
