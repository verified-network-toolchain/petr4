/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1670-bmv2.p4
\n
#include <core.p4>
#include <v1model.p4>

struct switch_metadata_t {
    bit<8> port;
}

header serialized_switch_metadata_t {
    switch_metadata_t meta;
}

struct parsed_packet_t {
    serialized_switch_metadata_t mirrored_md;
}

struct local_metadata_t {
}

parser parse(packet_in pk, out parsed_packet_t h, inout local_metadata_t local_metadata,
             inout standard_metadata_t standard_metadata) {
    state start {
	transition accept;
    }
}

control ingress(inout parsed_packet_t h, inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
    apply {
	h.mirrored_md.setValid();
	h.mirrored_md.meta = { 0 };
    }
}

control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
    apply { }
}

control deparser(packet_out b, in parsed_packet_t h) {
    apply { }
}

control verifyChecksum(inout parsed_packet_t hdr,
inout local_metadata_t local_metadata) {
    apply { }
}

control compute_checksum(inout parsed_packet_t hdr,
                         inout local_metadata_t local_metadata) {
    apply { }
}

V1Switch(parse(), verifyChecksum(), ingress(), egress(),
compute_checksum(), deparser()) main;
************************\n******** petr4 type checking result: ********\n************************\n
