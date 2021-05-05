#include <core.p4>
#include <v1model.p4>

enum bit<8> flag_t {
    ok = 0;
    not_ok = 1;
}

header hdr_t {
    flag_t flag;
}

struct headers {
    hdr_t h;
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
        h.h.flag = (flag_t)8w1;
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
