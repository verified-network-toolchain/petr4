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
        bool a = 8w8 == 8;
        bool b = 4 != 7w3;
        bool c = 7 < 19w12;
        bool d = 18w12 > 7;
        bool e = 6w7 <= 6w8;
        bool f = 9w7 <= 9w7;
        bool g = 6w8 >= 6w7;
        bool h = 9w7 >= 9w7; // all true
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
        bit<8> x = 4w2 ++ 4w10; //42
        bit<6> y = 12w3927[4w8:2w3]; //42
        bit z = 4w7[1w1:1w1]; //1
        // packet.emit((bit<8>) ((bit) a));
        // packet.emit((bit<8>) ((bit) b));
        // packet.emit((bit<8>) ((bit) c));
        // packet.emit((bit<8>) ((bit) d));
        // packet.emit((bit<8>) ((bit) e));
        // packet.emit((bit<8>) ((bit) f));
        // packet.emit((bit<8>) ((bit) g));
        // packet.emit((bit<8>) ((bit) h));
        // packet.emit(i);
        // packet.emit(j);
        // packet.emit(k);
        // packet.emit(l);
        // packet.emit(m);
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
        packet.emit((bit<8>) y);
        packet.emit((bit<8>) z);
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

/* lots of bugs */
