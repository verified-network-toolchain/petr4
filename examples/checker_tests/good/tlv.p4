#include <v1model.p4>
/* dependent grammar for a small TLV toy example: 
    a size(int)*n int[n] 
  | b size(int) int 
*/
const int MAX_LENGTH = 255;
const int SIZE_INT = 4;
typedef int<32> inner_t;

header byte_t {
  bit<8> val;
}
struct TV {
  byte_t length;
  byte_t[MAX_LENGTH] values;
} 
struct meta_t {
  bit<8> idx;
}

parser Parse(packet_in pkt, out TV output, inout meta_t meta,
             inout standard_metadata_t std_meta) {
  state start {
    meta.idx = 0;
    transition parse_array;
  }
  state parse_array {
    pkt.extract(output.length);
    transition select(output.length.val) {
      0: accept;
      1..MAX_LENGTH: parse_array_values;
    }
  }
  state parse_array_values {
    pkt.extract(output.values[meta.idx]);
    meta.idx = meta.idx + 1;
    transition select(meta.idx) {
      output.length.val: accept;
      default: parse_array_values;
    }
  }
}

// Our switch table comprises of IPv6 addresses vs. egress_port.
// This is the table we setup here.
control TLVIngress(inout TV hdr, inout meta_t meta,
                inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control TLVEgress(inout TV hdr, inout meta_t meta,
               inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control Deparse(packet_out packet, in TV hdr) {
    apply {
        packet.emit(hdr.length);
        packet.emit(hdr.values);
    }
}

control MyVerifyChecksum(inout TV hdr, inout meta_t meta) {
    apply {
    }
}

control Emp(inout TV hdr, inout meta_t meta) {
    apply {
    }
}

V1Switch(Parse(), Emp(), TLVIngress(), TLVEgress(), Emp(), Deparse()) main;
