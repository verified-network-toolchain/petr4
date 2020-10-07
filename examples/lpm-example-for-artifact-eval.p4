#include <core.p4>
#include <v1model.p4>

header hdr {
    bit<8>  ignored;
    bit<8>  key;
}

struct Header_t {
    hdr h;
}
struct Meta_t {}

parser p(packet_in b, out Header_t h, inout Meta_t m, inout standard_metadata_t sm) {
    state start {
        b.extract(h.h);
        transition accept;
    }
}

control vrfy(inout Header_t h, inout Meta_t m) { apply {} }
control update(inout Header_t h, inout Meta_t m) { apply {} }
control egress(inout Header_t h, inout Meta_t m, inout standard_metadata_t sm) { apply {} }
control deparser(packet_out b, in Header_t h) { apply { b.emit(h.h); } }

control ingress(inout Header_t h, inout Meta_t m, inout standard_metadata_t standard_meta) {

    action no_op() { }
    action set_port(bit<9> x) {
        standard_meta.egress_spec = x;
    }

    table t_lpm {

  	key = {
            h.h.key : lpm;
        }

	actions = {
            set_port;
        }

	default_action = set_port(3);

    }

    apply {
        t_lpm.apply();
    }
}


V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
