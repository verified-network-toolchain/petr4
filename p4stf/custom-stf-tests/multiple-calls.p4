#include <core.p4>
#include <v1model.p4>

header byte_t {
    bit<8> val;
}

struct hdr_t {
    byte_t f;
}
struct metadata { }

parser MyParser(packet_in packet,
                out hdr_t hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.f);
        transition accept;
    }
}

control MyChecksum(inout hdr_t hdr, inout metadata meta) {
    apply { }
}

bit<8> incr(inout bit<8> x) {
    x = x + 1;
    return x;
}

control C(inout bit<8> x) {
    bit<8> i = 1;
    apply {
        i = i + 1;
        x = i;
    }
}

control MyIngress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    C() c_inst;
    apply {
        c_inst.apply(h.f.val);
        c_inst.apply(h.f.val);
    }
}

control MyEgress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    apply { }
}

control MyDeparser(packet_out packet, in hdr_t hdr) {
    apply {
        packet.emit(hdr.f);
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
