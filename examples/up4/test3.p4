#include "core.p4"
#include "up4.p4"

header ethernet_t {
    bit<16>   etherType;
}

header ipv4_t {
    bit<4>    version;
    bit<4>    ihl;
}

header tcp_t{
    bit<16> srcPort;
    bit<16> dstPort;
}
struct headers {
    ethernet_t   ethernet;
    ipv4_t       ipv4;
    tcp_t        tcp;
}

struct metadata3 { }
struct in_param_t3 { }
struct out_param_t3 { }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition parse_ethernet;
    }

    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            42: parse_ipv4;
            default: accept;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol){
            33: tcp;
            default: accept;
        }
    }

    state tcp {
       packet.extract(hdr.tcp);
       transition accept;
    }
}

control MyControl(im_t im,
                  inout head3[13] hdrs,
                  inout metadata3 meta,
                  in in_param_t3 in_param,
                  out out_param_t3 out_param,
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
            hdrs[12] = { 33 };
        }
    }
}

control MyDeparser(packet_out packet, in head3[13] hdr) {
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
main1;
