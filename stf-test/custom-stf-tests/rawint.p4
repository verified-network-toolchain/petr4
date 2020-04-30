#include <core.p4>
#include <v1model.p4>

const bool a = 8 == 8;
const bool b = 4 != 7;
const bool c = 7 < 12;
const bool d = 12 > 7;
const bool e = 7 <= 8;
const bool f = 7 <= 7;
const bool g = 8 >= 7;
const bool h = 7 >= 7; // all true
const bit<8> i = -(214); //42
const bit<8> j = +(42); //42
const bit<8> k = (7 + 3) + 32; //42
const bit<8> l = 117 - 75; //42
const bit<8> m = 2 * 3 * 7; //42
const bit<8> n = 126 / 3; //42
const bit<8> o  = 292 % 50; //42


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
      packet.emit(n);
      packet.emit(o);
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
