#include "core.p4"
#include "up4.p4"

header head2 {
    bit<8> v;
}

header ipv4_t2 {
    bit<4>    version;
    bit<4>    ihl;
    bit<8>    diffserv;
    bit<16>   totalLen;
    bit<16>   identification;
    bit<3>    flags;
    bit<13>   fragOffset;
    bit<8>    ttl;
    bit<8>    protocol;
    bit<16>   hdrChecksum;
}

struct metadata2 { }
struct in_param_t2 { }
struct out_param_t2 { }

parser MyParser2(packet_in packet,
                im_t im,
                out head2[13] hdrs,
                inout metadata2 meta,
                in in_param_t2 in_param,
                inout error parser_error) {

    state start {
        packet.extract(hdrs[0]);
        transition select(packet.lookahead< bit<8> >()) {
            42 : next;
            11: accept;
            _ : reject;
        }
    }

    state next {
        hdrs.push_front(1);
        packet.extract(hdrs[0]);
        transition select(packet.lookahead< bit<8> >()) {
            33 : final;
            12: accept;
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

control MyControl2(im_t im,
                  inout head2[13] hdrs,
                  inout metadata2 meta,
                  in in_param_t2 in_param,
                  out out_param_t2 out_param,
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

control MyDeparser2(packet_out packet, in head2[13] hdr) {
    apply {
        packet.emit(hdr[0]);
        packet.emit(hdr);
    }
}

uP4Switch(
    MyParser2(),
    MyControl2(),
    MyDeparser2()
    )
main2;
