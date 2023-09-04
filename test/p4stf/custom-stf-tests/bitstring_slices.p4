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
    apply { }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        bit<8> a = 43;
        bit<8> b = (bit<8>) (a[6:2]); //10
        bit<8> c = 42 + 64;
        bit<8> d = (bit<8>) c[6:2]; //26
        bit<8> e = (bit<8>) a[0:0]; //1
        bit<8> f = (bit<8>) a[2:2]; //0
        bit<8> g = (bit<8>) a[1:1]; //1
        bit<8> h = (bit<8>) a[1:0]; //3
        bit<8> i = (bit<8>) a[5:4]; //2
        bit<8> j = 43;
        j[6:1] = 0; //1
        bit<8> k = 43;
        k[0:0] = 0; //42
        bit<8> l = 43;
        l[4:2] = 7; //63
        packet.emit(a);
        packet.emit(b);
        packet.emit(c);
        packet.emit(d);
        packet.emit(e);
        packet.emit(f);
        packet.emit(g);
        packet.emit(h);
        packet.emit(i);
        packet.emit(j);
        packet.emit(k);
        packet.emit(l);
     }
}

//this is declaration
V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    ) main;
