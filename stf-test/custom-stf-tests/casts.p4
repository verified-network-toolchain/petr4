#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

typedef bit<32> u32;
type int<32> s32;

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
        bool a = (bool) 1w1; //true
        bit<4> b = (bit<4>) 8w0b00011111; //15
        bit<4> c = (bit<4>) 4s0b1111; //15
        bit<4> d = 20; //4
        int<4> e = (int<4>)(int<8>) 8w0b10001111; //-1
        int<4> f = (int<4>) 4w0b1111; //-1
        int<4> g = 24; //-8

        u32 h = 5;
        bit<32> i = (bit<32>) h;
        int<32> j = (int<32>) h;
        u32 k = (u32) 5;

        int<32> l = 6;
        s32 m = (s32) l;
        packet.emit((bit<8>) ((bit) a));
        packet.emit((bit<8>) b);
        packet.emit((bit<8>) c);
        packet.emit((bit<8>) d);
        packet.emit((int<8>) e);
        packet.emit((int<8>) f);
        packet.emit((int<8>) g);
        packet.emit(h);
        packet.emit(i);
        packet.emit(j);
        packet.emit(k);
        packet.emit(l);
        packet.emit(m); 
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
