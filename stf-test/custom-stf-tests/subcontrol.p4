#include <core.p4>
#include <v1model.p4>

header bitehdr {
  bit<8> v;
}

struct metadata { }

error { MyError }


parser MyParser(packet_in packet,
                out bitehdr[11] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition accept;
    }
}

control MyChecksum(inout bitehdr[11] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout bitehdr[11] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {

    }
}

control ChangeEgressSpec(inout bitehdr[11] hdr) {
    apply {
        hdr[1].v = 8w7;
        hdr[1].setValid();
        exit;
    }
}

control MyEgress(inout bitehdr[11] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    ChangeEgressSpec() subcontrol;
    apply {
        subcontrol.apply(hdr);
        hdr[0].setValid();
        hdr[0].v = 8w42;
    }
}

control MyDeparser(packet_out packet, in bitehdr[11] hdr) {
    apply {
        packet.emit(hdr[0]);
        packet.emit(hdr[1]);
    }
}

//TODO: blocking on the stf update

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
