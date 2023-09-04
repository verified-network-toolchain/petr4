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
      bool a = - (8s8) == -8;
      bool b = 4 != -(8s3);
      bool c = -7 < 19s12;
      bool d = 18s12 > -7;
      bool e = -(6s8) <= -(6s7);
      bool f = 9s7 <= 9s7;
      bool g = 6s8 >= 6s7;
      bool h = 9s7 >= 9s7; // all true
      int<8> i = -(8s214); //42
      int<8> j = +(8s42); //42
      int<8> k = (-8s7 + -8s3) + 52; //42
      int<8> l = (-8s42) - (-8s84); //42
      int<8> m = -8s2 * 3 * -8s7; //42
      int<8> r = 8s7 |+| 8s3 |+| 32; //42
      int<8> s = 8s117 |-| 8s75; //42
      int<8> t = 8s7 + 8s3 + 8s32 + 128 + 8s128; //42, should wrap around
      int<8> u = 8s117 - 8s75 - 8s128 - 8s128; //42, should wrap around
      int<8> v = 8s7 |+| 8s3 |+| 8s32 |+| 8s128 |+| 8s128; //127, should saturate
      int<8> w = 8s117 |-| 8s75 |-| 8s128 |-| 8s128; //-128, should saturate
      packet.emit((bit<8>) ((bit) a));
      packet.emit((bit<8>) ((bit) b));
      packet.emit((bit<8>) ((bit) c));
      packet.emit((bit<8>) ((bit) d));
      packet.emit((bit<8>) ((bit) e));
      packet.emit((bit<8>) ((bit) f));
      packet.emit((bit<8>) ((bit) g));
      packet.emit((bit<8>) ((bit) h));
      packet.emit(i);
      packet.emit(j);
      packet.emit(k);
      packet.emit(l);
      packet.emit(m);
      // packet.emit(r);
      // packet.emit(s);
      // packet.emit(t);
      // packet.emit(u);
      // packet.emit(v);
      // packet.emit(w);
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


