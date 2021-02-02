#include <core.p4>
#include <up4.p4>

struct empty_t { }
struct hdr_t { }

parser MyParser1(packet_in packet,
		 im_t im,
		 out hdr_t hdrs,
		 inout empty_t meta,
		 in empty_t in_param,
		 inout empty_t inout_param) {
    state start {
        transition accept;
    }
}

control MyControl1(im_t im,
                   inout hdr_t hdrs,
                   inout empty_t meta,
                   in empty_t in_param,
                   out empty_t out_param,
                   inout empty_t inout_param) {
    apply {
    }
}

control MyDeparser1(packet_out packet,
                    in hdr_t hdrs) {
    apply {
    }
}

uP4Switch(MyParser1(), MyControl1(), MyDeparser1()) main;