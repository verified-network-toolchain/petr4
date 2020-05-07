#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

void swap(inout bit a, inout bit b) {
  bit tmp = a;
  a = b;
  b = tmp;
  return;
}

void swapped(inout bit<2> x) {
  swap(x[1:1], x[0:0]);
}

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
        bit<2> a = 0;
        bit<2> b = 1;
        bit<2> c = 2;
        bit<2> d = 3;
        swapped(a); //0
        swapped(b); //2
        swapped(c); //1
        swapped(d); //3
        packet.emit((bit<8>) a);
        packet.emit((bit<8>) b);
        packet.emit((bit<8>) c);
        packet.emit((bit<8>) d);
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
