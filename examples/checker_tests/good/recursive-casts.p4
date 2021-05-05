#include <core.p4>
#include <v1model.p4>

header hdr_t {
    bit<8> x;
}

struct headers {
    hdr_t h;
}

header hdr2_t {
    bit<4> y;
}

struct headers2 {
    hdr2_t h;
}

struct empty_t {}

parser p(packet_in pk, out headers h, inout empty_t m, inout standard_metadata_t sm) {
    state start {
	pk.extract(h.h);
	transition accept;
    }
}

control deparser(packet_out pk, in headers h) {
    apply {
	pk.emit(h.h);
    }
}

/* "concatenation is applied to two bit-strings (signed or
unsigned)... and the sign of the result is taken from the left
operand." (reference: 8.5, 8.6 and 8.6.1) */
control ingress(inout headers h, inout empty_t m, inout standard_metadata_t sm) {
    apply {
	headers2 h2 = {h = {y = 0}};
        h = (headers)h2;
    }
}

control egress(inout headers h, inout empty_t m, inout standard_metadata_t sm) {
    apply {
    }
}

control nop(inout headers h, inout empty_t m) {
    apply {
    }
}

V1Switch(p(), nop(), ingress(), egress(), nop(), deparser()) main;