#include <core.p4>
#include <v1model.p4>

header head {
  bit<8> v;
}

struct metadata { }

error { MyError }

parser MySubParser(packet_in packet, inout head[11] hdr, standard_metadata_t standard_metadata) {

    state start {
        /*
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            1 : first;
            default : pre_reject;
        }
        */
        transition accept;
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
        verify(false, error.MyError);
        transition reject;
    }
}

parser MyParser(packet_in packet,
                out head[11] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    MySubParser() subparser;

    state start {
        /*
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            42 : start;
            0 : accept;
            _ : evoke_subparser;
        }
        */
        transition accept;
    }

    state evoke_subparser {
        subparser.apply(packet, hdr, standard_metadata);
        hdr.pop_front(1);
        packet.extract(hdr[10]);
        transition select(hdr[10].v) {
            42 : start;
            0 : accept;
        }
    }
}

control MyChecksum(inout head[11] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout head[11] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        if (standard_metadata.parser_error == error.NoError) {
            exit;
        }
        else {
            standard_metadata.egress_spec = 7;
            hdr.push_front(11);
            hdr[0] = {42};
            hdr[1] = {0};
            hdr[2] = {0};
            hdr[3] = {0};
            hdr[4] = {0};
            hdr[5] = {0};
            hdr[6] = {0};
            hdr[7] = {42};
            hdr[8] = {0};
            hdr[9] = {0};
            hdr[10] = {42};
        }
    }
}

control MyEgress(inout head[11] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in head[11] hdr) {
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
