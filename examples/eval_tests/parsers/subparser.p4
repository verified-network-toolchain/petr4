#include <core.p4>
#include <v1model.p4>

header bitehdr {
  bit<8> v;
}

struct metadata { }

error { MyError }

parser MySubParser(packet_in packet, inout bitehdr[11] hdr, standard_metadata_t standard_metadata) {

    state start {
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            1 : first;
            default : pre_reject;
        }
    }

    state first {
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            2 : second;
            default : pre_reject;
        }
    }

    state second {
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            3 : third;
            default : pre_reject;
        }
    }

    state third {
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            4 : accept;
            default : pre_reject;
        }
    }

    state pre_reject {
        standard_metadata.parser_error = error.MyError;
        transition reject;
    }
}

parser MyParser(packet_in packet,
                out bitehdr[11] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    MySubParser() subparser;

    state start {
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            42 : start;
            0 : accept;
            _ : evoke_subparser;
        }
    }

    state evoke_subparser {
        MySubParser.apply(packet, hdr, standard_metadata);
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            42 : start;
            0 : accept;
        }
    }
}

control MyChecksum(inout bitehdr[11] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout bitehdr[11] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        if (standard_metadata.parser_error == error.NoError) {
            exit;
        }
        else {
            hdr.push_front(15);
        }
    }
}

control MyEgress(inout bitehdr[11] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in bitehdr[11] hdr) {
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
