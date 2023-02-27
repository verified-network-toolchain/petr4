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

bit<8> f(inout bit<8> y) {
  y = 0;
  return 0;
}

bit<8> g(inout bit<8> y) { y = 1; return 1; }

control MyIngress(inout hdr_t hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  bit<8> y = 0xFF;
  bit<8> z = true ? f(y) : g(y);
  apply {
    hdr.h.f = y;
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
