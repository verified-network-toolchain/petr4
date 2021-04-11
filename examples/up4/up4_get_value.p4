#include "core.p4"
#include "up4.p4"

header head1 {
    bit<8> v;
}

struct metadata1 { }
struct in_param_t1 { }
struct out_param_t1 { }

parser MyParser1(packet_in packet,
                im_t im,
                out head1[13] hdrs,
                inout metadata1 meta,
                in in_param_t1 in_param,
                inout error parser_error) {

    state start {
        packet.extract(hdrs[0]);
        transition select(packet.lookahead< bit<8> >()) {
            42 : next;
            _ : reject;
        }
    }

    state next {
        hdrs.push_front(1);
        packet.extract(hdrs[0]);
        transition select(packet.lookahead< bit<8> >()) {
            42 : next;
            33 : final;
            _ : reject;
        }
    }

    state final {
        hdrs.push_front(1);
        packet.extract(hdrs[0]);
        parser_error = error.NoError;
        transition accept;
    }

}

control MyControl1(im_t im,
                  inout head1[13] hdrs,
                  inout metadata1 meta,
                  in in_param_t1 in_param,
                  out out_param_t1 out_param,
                  inout error parser_error) {
    apply {
        if (parser_error == error.NoError) {
            hdrs[0] = { 72 };
            hdrs[1] = { 101 };
            hdrs[2] = { 108 };
            hdrs[3] = { 108 };
            hdrs[4] = { 111 };
            hdrs[5] = { 44 };
            hdrs[6] = { 32 };
            hdrs[7] = { 87 };
            hdrs[8] = { 111 };
            hdrs[9] = { 114 };
            hdrs[10] = { 108 };
            hdrs[11] = { 100 };
            hdrs[12] = { (bit<8>) im.get_value(metadata_fields_t.QUEUE_DEPTH_AT_DEQUEUE) };
        }
    }
}

control MyDeparser1(packet_out packet, in head1[13] hdr) {
    apply {
        packet.emit(hdr[0]);
        packet.emit(hdr);
    }
}

uP4Switch(
    MyParser1(),
    MyControl1(),
    MyDeparser1()
    )
main1;
