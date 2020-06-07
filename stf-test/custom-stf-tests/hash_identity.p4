#include <core.p4>
#include <v1model.p4>

const bit<121> max = 121w1 << 120;

header my_header {
  bit<8> first;
  bit<32> second;
  bit<64> third;
  bit<16> fourth;
}

header result_header {
  bit<120> first;
}

struct metadata { }
struct headers { 
    my_header pkt_hdr;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.pkt_hdr);
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
    result_header result;
    apply {
        hash(result.first, HashAlgorithm.identity, 8w0,
              { hdr.pkt_hdr.first, hdr.pkt_hdr.second, hdr.pkt_hdr.third, hdr.pkt_hdr.fourth }, max);
        packet.emit(result);
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
