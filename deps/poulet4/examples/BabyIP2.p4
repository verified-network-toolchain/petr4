#include <core.p4>
#include <v1model.p4>

header silly_combined_hdr {
    bit<8> src;
    bit<8> dst;
    bit<4> proto;
    bit<8> t_or_u_sport;
    bit<8> t_or_u_dport;
    bit<4> t_or_u_flags;
}

header tcp_seq_suffix {
    bit<8> seq;
}

struct metadata { }
struct headers {
    silly_combined_hdr comb;
    tcp_seq_suffix opt_suff;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.comb);
        transition select(hdr.comb.proto) {
            1 : accept;
            0 : parse_tcp;
            default : reject;
        }
    }

    state parse_tcp {
        packet.extract(hdr.opt_suff);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
      if (hdr.opt_suff.isValid()) {
          standard_metadata.egress_spec = 0;
      }
      else {
          standard_metadata.egress_spec = 1;
      }
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.comb);
        packet.emit(hdr.opt_suff);
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
    )
main;
