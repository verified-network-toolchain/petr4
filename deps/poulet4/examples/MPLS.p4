#include <core.p4>
#include <v1model.p4>

header mpls_entry {
  bit<20> label;
  bit<3> class;
  bit bos_marker;
  bit<8> ttl;
}

const bit<3> MAX_MPLS_ENTRIES = 3w4;

struct mpls_h {
  mpls_entry[MAX_MPLS_ENTRIES] mpls_stack;
  bit<3> bos;
}

struct metadata { }

parser MPLSNormalParser(
  packet_in packet,
  out mpls_h hdr,
  inout metadata meta,
  inout standard_metadata_t standard_metadata) {
    
  state start {
    hdr.bos = 3w0; 
    transition parse_mpls_entry;
  }

  state parse_mpls_entry {
    packet.extract(hdr.mpls_stack.next);
    hdr.bos = hdr.bos + 3w1;
    transition select(hdr.mpls_stack.last.bos_marker) {
      0 : parse_mpls_entry;
      1 : accept;
      default: reject;
    }
  }
}

parser MPLSFixedWidthParser(
  packet_in packet,
  out mpls_h hdr,
  inout metadata meta,
  inout standard_metadata_t standard_metadata) {
    
  state start {
    hdr.bos = 3w0; 
    transition parse_mpls_entry;
  }

  state parse_mpls_entry {
    packet.extract(hdr.mpls_stack.next);
    hdr.bos = hdr.bos + 3w1;
    transition select(hdr.mpls_stack.last.bos_marker) {
      0 : parse_mpls_entry;
      1 : skip_remaining;
      default: reject;
    }
  }

  state skip_remaining { 
    packet.advance((bit<32>)(MAX_MPLS_ENTRIES - hdr.bos) * 32w32);
    transition accept;
  }
}

parser MPLSVectorizedParser(packet_in packet,
                            out mpls_h hdr,
                            inout metadata meta,
                            inout standard_metadata_t standard_metadata) {
    
  state start {
    packet.extract(hdr.mpls_stack[3w0]);
    packet.extract(hdr.mpls_stack[3w1]);
    packet.extract(hdr.mpls_stack[3w2]);
    packet.extract(hdr.mpls_stack[3w3]);
    transition select(hdr.mpls_stack[3w0].bos_marker, hdr.mpls_stack[3w1].bos_marker, hdr.mpls_stack[3w2].bos_marker, hdr.mpls_stack[3w3].bos_marker) {
      (1, _, _, _) : set_0;
      (0, 1, _, _) : set_1;
      (0, 0, 1, _) : set_2;
      (0, 0, 0, 1) : set_3;
      default : reject;
    }
  }

  state set_0 {
    hdr.bos = 3w0;
    transition accept;
  }

  state set_1 {
    hdr.bos = 3w1;
    transition accept;
  }

  state set_2 {
    hdr.bos = 3w2;
    transition accept;
  }

  state set_3 {
    hdr.bos = 3w3;
    transition accept;
  }
}

// parser MPLSVectOptParser(packet_in packet,
//                             out mpls_h hdr,
//                             inout metadata meta,
//                             inout standard_metadata_t standard_metadata) {
    
//   state start {
//     packet.extract(hdr.mpls_stack[0]);
//     packet.extract(hdr.mpls_stack[1]);
//     packet.extract(hdr.mpls_stack[2]);
//     packet.extract(hdr.mpls_stack[3]);
//     // bitwise operations to calculate the length of the mpls_stack and 0 if all of the
//     // bos_marker fields are 0.
//     // TODO: expression for including mpls_stack[3]
//     hdr.bos = hdr.mpls_stack[0] | 
//               ((~ hdr.mpls_stack[0] & hdr.mpls_stack[1]) << 1) | 
//               ((~ hdr.mpls_stack[0] & ~ hdr.mpls_stack[1] & hdr.mpls_stack[2]) << 1 + (~ hdr.mpls_stack[0] & ~ hdr.mpls_stack[1] & hdr.mpls_stack[2])); 
//     transition select((hdr.mpls_stack[0].bos_marker, hdr.mpls_stack[1].bos_marker, hdr.mpls_stack[2].bos_marker, hdr.mpls_stack[3].bos_marker)) {
//       (1, _, _, _) : set_0;
//       (0, 1, _, _) : set_1;
//       (0, 0, 1, _) : set_2;
//       (0, 0, 0, 1) : set_3;
//       default : reject;
//     }
//   }

//   state set_0 {
//     hdr.bos = 0;
//     transition accept;
//   }

//   state set_1 {
//     hdr.bos = 1;
//     transition accept;
//   }

//   state set_2 {
//     hdr.bos = 2;
//     transition accept;
//   }

//   state set_3 {
//     hdr.bos = 3;
//     transition accept;
//   }
// }

control MyChecksum(inout mpls_h hdr, inout metadata meta) {
  apply { }
}

control MyIngress(inout mpls_h hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  apply { }
}

control MyEgress(inout mpls_h hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
  apply { }
}

control MyDeparser(packet_out packet, in mpls_h hdr) {
  apply {
    packet.emit(hdr);
  }
}

V1Switch(
  MPLSFixedWidthParser(),
  MyChecksum(),
  MyIngress(),
  MyEgress(),
  MyChecksum(),
  MyDeparser()
  )
main;
