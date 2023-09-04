#include <core.p4>
#include <v1model.p4>
typedef standard_metadata_t std_meta_t;

header h_t {
  bit<8> x;
}

struct H {
  h_t h;
}

struct M {
}

parser ParserI(packet_in pk, out H hdr, inout M meta, inout std_meta_t std_meta) {
    state start {
        pk.extract(hdr.h);
        transition accept;
    }
}

control VerifyChecksumI(inout H hdr, inout M meta) {
    apply { }
}

control ComputeChecksumI(inout H hdr, inout M meta) {
    apply { }
}

action g(inout bit<8> b) { b = ~b; }

action f(inout bit<8> b) { g(b); }

control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
  action g(inout bit<8> b) { b = 0x99; }
  apply {
    f(hdr.h.x);
  }
}

control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
    apply { }
}

control DeparserI(packet_out b, in H hdr) {
    apply {
        b.emit(hdr.h);
    }
}

V1Switch(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
