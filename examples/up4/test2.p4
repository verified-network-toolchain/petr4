#include <core.p4>
#include <up4.p4>

struct empty2_t { }
struct hdr2_t { }

parser MyParser2(packet_in packet,
		 im_t im,
		 out hdr2_t hdrs,
		 inout empty2_t meta,
		 in empty2_t in_param,
		 inout empty2_t inout_param) {
    state start {
        transition accept;
    }
}

control MyControl2(im_t im,
                   inout hdr2_t hdrs,
                   inout empty2_t meta,
                   in empty2_t in_param,
                   out empty2_t out_param,
                   inout empty2_t inout_param) {
    apply {
    }
}

control MyDeparser2(packet_out packet,
                    in hdr2_t hdrs) {
    apply {
    }
}

uP4Switch(MyParser2(), MyControl2(), MyDeparser2()) main2;
