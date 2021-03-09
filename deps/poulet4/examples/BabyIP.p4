#include <core.p4>
#include <v1model.p4>

header baby_ip {
    bit<8> src;
    bit<8> dst;
    bit<4> proto;
}

header baby_tcp {
    bit<8> sport;
    bit<8> dport;
    bit<4> flags;
    bit<8> seq;
}

header baby_udp {
    bit<8> sport;
    bit<8> dport;
    bit<4> flags;
}

header_union btcp_or_budp {
    baby_udp udp;
    baby_tcp tcp;
}   

struct metadata { }
struct headers {
    baby_ip ip;
    btcp_or_budp t_or_u;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.ip);
        transition select(hdr.ip.proto) {
            1 : parse_udp;
            0 : parse_tcp;
            default : reject;
        }
    }

    state parse_udp {
        packet.extract(hdr.t_or_u.udp);
        transition accept;
    }

    state parse_tcp {
        packet.extract(hdr.t_or_u.tcp);
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
      if (hdr.t_or_u.tcp.isValid()) {
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
        packet.emit(hdr.ip);
        packet.emit(hdr.t_or_u);
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
