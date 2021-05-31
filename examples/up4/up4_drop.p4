#include "core.p4"
#include "up4.p4"

header head {
    bit<8> v;
}

header head5 {
    bit<8> v;
}

header ipv4_t {
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

struct metadata { }
struct in_param_t { }
struct out_param_t { }

parser MyParser1(packet_in packet,
                im_t im,
                out head[13] hdrs,
                inout metadata meta,
                in in_param_t in_param,
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

control MyControl1(im_t im,
                  inout head[13] hdrs,
                  inout metadata meta,
                  in in_param_t in_param,
                  out out_param_t out_param,
                  inout error parser_error) {
    apply {
        im.drop();
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
            hdrs[12] = { 33 };
        }
    }
}

control MyDeparser1(packet_out packet, in head[13] hdr) {
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
