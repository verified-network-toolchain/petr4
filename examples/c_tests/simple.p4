#include "core.p4"

header simple_h {
    bit<8>  src;
    bit<8>  dst;
}

struct header_t {
  simple_h simple;
}

parser P(packet_in pkt, inout header_t hdrs) {
    state start {
        pkt.extract(hdrs.simple);
        transition accept;
    }
}

control C(inout header_t hdrs, out bool forward) {
    action forward() {
        forward = true;
    }
    action drop() {
        forward = false;
    }
    table t {
        key = { hdrs.simple.dst : exact; }
        actions = { forward; drop; }
    }
    apply {
        t.apply();
    }
}

control D(packet_out pkt, in header_t hdrs) {
    apply {
        pkt.emit(hdrs.simple);
    }
}

package S(P p, C vr, D dep);
S(P(), C(), D()) main;