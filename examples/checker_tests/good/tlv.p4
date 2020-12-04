#include <v1model.p4>
/* dependent grammar for a small TLV toy example: 
    a size(int)*n int[n] 
  | b size(int) int 
*/
const int MAX_LENGTH = 255;
const int SIZE_INT = 4;
typedef int<32> inner_t;

header byte_t {
  bit<8> v;
}
struct TV {
  byte_t length;
  byte_t[MAX_LENGTH] values;
} 
struct meta_t {
  bit<8> idx;
}

parser Parse(packet_in pkt, out TV hdr, inout meta_t meta,
             inout standard_metadata_t std_meta) {
  state start {
    meta.idx = 0;
    transition parse_array;
  }
  state parse_array {
    pkt.extract(hdr.length);
    transition select(hdr.length.v) {
      0: accept;
      1..MAX_LENGTH: parse_array_values;
    }
  }
  state parse_array_values {
    pkt.extract(hdr.values[meta.idx]);
    meta.idx = meta.idx + 1;
    transition select(meta.idx) {
      hdr.length.v: accept;
      default: parse_array_values;
    }
  }
}

// Our switch table comprises of IPv6 addresses vs. egress_port.
// This is the table we setup here.
control TLVIngress(inout TV hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    apply {
        // operations on array and length have to be synced up
        if (hdr.length.v > 0 && hdr.values[hdr.length.v - 1].isValid()) {
            hdr.length.v = hdr.length.v - 1;
            hdr.values[hdr.length.v].setInvalid();
        }
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
