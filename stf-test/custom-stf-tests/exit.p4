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
        packet.extract(hdr[0]);
        transition select(packet.lookahead< bit<8> >()) {
            8w42 : next;
            _ : reject;
        }
    }

    state next {
        hdr.push_front(1);
        packet.extract(hdr[0]);
        transition select(packet.lookahead< bit<8> >()) {
            8w42 : next;
            8w33 : final;
            _ : reject;
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
    apply {

    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

    action a() {
        if (true) {
            exit;
        }
        else {
            standard_metadata.egress_spec = 42;
        }
    }

    action b() {
        if (true) {
            a();
        }
        else {
            standard_metadata.egress_spec = 24;
        }
    }

    apply {
        b();
    }
}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        hdr[0] = { 72 };
        hdr[1] = { 101 };
        hdr[2] = { 108 };
        hdr[3] = { 108 };
        hdr[4] = { 111 };
        hdr[5] = { 44 };
        hdr[6] = { 32 };
        hdr[7] = { 87 };
        hdr[8] = { 111 };
        hdr[9] = { 114 };
        hdr[10] = { 108 };
        hdr[11] = { 100 };
        hdr[12] = { 33 };
        packet.emit(hdr);
    }
}

//TODO: blocking this test on the stf update for tables

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
