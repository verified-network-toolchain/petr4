#include "core.p4"

/* Begin dummy architecture */
parser P<T>(packet_in pkt, inout T hdrs);
control C<T>(inout T hdrs, out bool forward);
control D<T>(packet_out pkt, in T hdrs);
package S<T>(P<T> p, C<T> c, D<T> d);
/* End dummy architecture */

header simple_h {
    bit<8>  src;
    bit<8>  dst;
}

struct header_t {
  simple_h simple;
}

parser MyP(packet_in pkt, inout header_t hdrs) {
    state start {
        pkt.extract(hdrs.simple);
        transition accept;
    }
}

control MyC(inout header_t hdrs, out bool forward) {
    action do_forward() {
        forward = true;
    }
    action do_drop() {
        forward = false;
    }
    table t {
        key = { hdrs.simple.dst : exact; }
        actions = { do_forward; do_drop; }
        default_action = do_drop;
        const entries = {
            0x0: do_forward();
        }
    }
    apply {
        t.apply();
    }
}

control MyD(packet_out pkt, in header_t hdrs) {
    apply {
        pkt.emit(hdrs.simple);
    }
}

S(MyP(), MyC(), MyD()) main;
