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
        // bit<8> a = (bit<8>) 8w8 == 8;
        // bit<8> b = (bit<8>) 4 != 7w3;
        // bit<8> c = (bit<8>) 7 < 19w12;
        // bit<8> d = (bit<8>) 18w12 > 7;
        // bit<8> e = (bit<8>) 6w7 <= 6w8;
        // bit<8> f = (bit<8>) 9w7 <= 9w7;
        // bit<8> g = (bit<8>) 6w8 >= 6w7;
        // bit<8> h = (bit<8>) 9w7 >= 9w7; // all true
        bit<8> i = -(214); //42
        bit<8> j = +(8w42); //42
        bit<8> k = (8w7 + 8w3) + 32; //42
        bit<8> l = 8w117 - 8w75; //42
        bit<8> m = 8w2 * 3 * 8w7; //42
        bit<8> n = 8w46 & 59; //42
        bit<8> o = 34 | 8w8; //42
        bit<8> p = ~ 8w42; //213
        bit<8> q = 8w25 ^ 51; //42
        bit<8> r = 8w7 |+| 8w3 |+| 32; //42
        bit<8> s = 8w117 |-| 8w75; //42
        bit<8> t = 8w7 + 8w3 + 8w32 + 128 + 8w128; //42, should wrap around
        bit<8> u = 8w117 - 8w75 - 8w128 - 8w128; //42, should wrap around
        bit<8> v = 8w7 |+| 8w3 |+| 8w32 |+| 8w128 |+| 8w128; //255, should saturate
        bit<8> w = 8w117 |-| 8w75 |-| 8w128 |-| 8w128; //0, should saturate
        bit<8> x = 2 ++ 4w10; //42
        //bit<6> y = 12w3927[4w8:2w3]; //42
        //bit<8> z = (bit<8>) 4w7[1w1:1w1]; //1
        // packet.emit(a);
        // packet.emit(b);
        // packet.emit(c);
        // packet.emit(d);
        // packet.emit(e);
        // packet.emit(f);
        // packet.emit(g);
        // packet.emit(h);
        packet.emit(i);
        packet.emit(j);
        packet.emit(k);
        packet.emit(l);
        packet.emit(m);
        packet.emit(n);
        packet.emit(o);
        packet.emit(p);
        packet.emit(q);
        packet.emit(r);
        packet.emit(s);
        packet.emit(t);
        packet.emit(u);
        packet.emit(v);
        packet.emit(w);
        packet.emit(x);
        //packet.emit(y);
        //packet.emit(z);
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
