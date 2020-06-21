#include <core.p4>
#include <v1model.p4>

const bit<32> reg_size = 128;

header my_header_t {
    bit<32> h;
}

struct metadata { }
struct headers {
    my_header_t h;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.h);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) { 

    apply { }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    register<bit<32>>(reg_size) r;
    bit<32> index;
    bit<32> reg_read_val;
    bit<32> reg_write_val;
    apply {
        index = 2;
        reg_write_val = hdr.h.h;
        r.read(reg_read_val, index);
        r.write(index, reg_write_val);

        packet.emit(reg_read_val);
    }
}

//this is declaration
V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
