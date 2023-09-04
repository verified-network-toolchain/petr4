#include <core.p4>
#include <up4.p4>

header head {
    bit<8> v;
}

struct metadata { }
struct in_param_t { }
struct out_param_t { }

<<<<<<<< HEAD:p4stf/custom-stf-tests/up4_im_t.p4
========
// commenting out b/c already defined in up4.p4
//typedef bit<9> PortId_t;
>>>>>>>> poulet4:p4stf/excluded/up4_im_t.p4
const PortId_t TEMP_PORT = 244;
const PortId_t OUT_PORT = 255;

parser MyParser(packet_in packet,
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

control MyControl(im_t im,
                  inout head[13] hdrs,
                  inout metadata meta,
                  in in_param_t in_param,
                  out out_param_t out_param,
                  inout error parser_error) {
    apply {
        im.set_out_port(TEMP_PORT);
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
            hdrs[11] = { (bit<8>) im.get_in_port() };
            hdrs[12] = { (bit<8>) im.get_out_port() };
        }
        im.set_out_port(OUT_PORT);
    }
}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr[0]);
        packet.emit(hdr);
    }
}

uP4Switch(
    MyParser(),
    MyControl(),
    MyDeparser()
    )
main;
