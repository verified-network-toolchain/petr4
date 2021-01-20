typedef bit<32> ethernet_h;
typedef bit<32> ipv4_h;

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader,
                    in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

struct headers {
  ethernet_h ether;
  ipv4_h ipv4;
}

parser P(packet_in pkt, inout headers hdrs) {
    state start {
        pkt.extract(hdrs.ether);
        transition ipv4;
    }
    state ipv4 {
        pkt.extract(hdrs.ipv4);
        transition accept;
    }
}

control C(inout headers hdrs, out bool forward) {
    action forward() {
        forward = true;
    }
    action drop() {
        forward = false;
    }
    table t {
        key = { ipv4.dst : exact; }
        actions = { forward; drop; }
    }
    apply {
        t.apply();
    }
}

control D(packet_out pkt, in headers hdrs) {
    apply {
        pkt.emit(hdrs.ether);
        pkt.emit(hdrs.ipv4);
    }
}

package S<H, M>(P<H, M> p, C<H, M> vr, D<H, M> dep);

S(P(), C(), D()) main;