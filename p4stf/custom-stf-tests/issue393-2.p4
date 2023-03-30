#include <core.p4>
#include <v1model.p4>
struct metadata { }
header h_t {
  bit<8> f;
}
struct hdr_t {
  h_t h;
}

parser MyParser(packet_in packet,
                out hdr_t hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
  state start {
    packet.extract(hdr.h);
    transition accept;
  }
}

control MyChecksum(inout hdr_t hdr, inout metadata meta) {
  apply { }
}

control C(inout h_t h, in bool x) {
  bit<8> x = 0xFF;
  action nop() { h.f = x; }
  apply {
    nop();
  }   
}

control MyIngress(inout hdr_t hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  C() c;
  apply {
    c.apply(hdr.h, false);
  }
}

control MyEgress(inout hdr_t hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in hdr_t hdr) {
  apply { 
    packet.emit(hdr.h);
  }
}

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    ) main;
