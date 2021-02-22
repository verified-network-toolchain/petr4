#include <core.p4>
#include <up4.p4>

struct empty1_t { }
struct hdr1_t { }

parser MyParser1(packet_in packet,
		 im_t im,
		 out hdr1_t hdrs,
		 inout empty1_t meta,
		 in empty1_t in_param,
		 inout empty1_t inout_param) {
    state start {
        transition accept;
    }
}

control MyControl1(im_t im,
                   inout hdr1_t hdrs,
                   inout empty1_t meta,
                   in empty1_t in_param,
                   out empty1_t out_param,
                   inout empty1_t inout_param) {
    apply {
    }
}

control MyDeparser1(packet_out packet,
                    in hdr1_t hdrs) {
    apply {
    }
}

uP4Switch(MyParser1(), MyControl1(), MyDeparser1()) main1;
