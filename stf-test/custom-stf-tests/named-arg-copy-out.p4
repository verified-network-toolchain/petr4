#include <core.p4>
#include <v1model.p4>

header byte_t {
    bit<8> val;
}

struct hdr_t {
    byte_t[10] arr;
}
struct metadata { }

void f(inout byte_t x, inout byte_t y) {
    x.val = 0xAA;
    y.val = 0xBB;
}


parser MyParser(packet_in packet,
                out hdr_t hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.arr.next);
        packet.extract(hdr.arr.next);
        packet.extract(hdr.arr.next);
        packet.extract(hdr.arr.next);
        packet.extract(hdr.arr.next);
        packet.extract(hdr.arr.next);
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

control MyIngress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    apply {
        bit<8> idx = 0;
        // 00 00
        f(y=h.arr[1], x=h.arr[1]);
        // AA 00 (if by arg order)
        f(x=h.arr[2], y=h.arr[2]);
        // AA BB (if by arg order)
    }
}

control MyEgress(inout hdr_t h, inout metadata meta, inout standard_metadata_t
std_meta) {
    apply { }
}

control MyDeparser(packet_out packet, in hdr_t hdr) {
    apply {
        packet.emit(hdr.arr);
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
