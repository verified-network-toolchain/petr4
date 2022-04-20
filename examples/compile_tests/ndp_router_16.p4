#include <core.p4>
#include <v1model.p4>

/*
*   ALLERT: all standard_metadata.egress_priority has been temporarily changed to standard_metadata.egress_spec
*   in order to successfully translate to P4-16
*   REASON: egress_priority is not currently supported in the standard metadata
*/

struct meta_t {
    bit<16> register_tmp;
    bit<16> ndpflags;
}

struct routing_metadata_t {
    bit<32> nhop_ipv4;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

header ndp_t {
    bit<16> flags;
    bit<16> checksum;
    bit<32> sport;
    bit<32> dport;
    bit<32> seqpull;
    bit<32> pacerecho;
}

struct metadata {
    @name(".meta") 
    meta_t             meta;
    @name(".routing_metadata") 
    routing_metadata_t routing_metadata;
}

struct headers {
    @name(".ethernet") 
    ethernet_t ethernet;
    @name(".ipv4") 
    ipv4_t     ipv4;
    @name(".ndp") 
    ndp_t      ndp;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".parse_ethernet") state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    @name(".parse_ipv4") state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            8w199: parse_ndp;
            default: accept;
        }
    }
    @name(".parse_ndp") state parse_ndp {
        packet.extract(hdr.ndp);
        transition accept;
    }
    @name(".start") state start {
        transition parse_ethernet;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".buffersense") register<bit<16>>(32w4) buffersense;
    @name(".decreasereg") action decreasereg() {
        buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port);
        buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp - 16w1 + (bit<16>)standard_metadata.egress_spec));
    }
    @name(".cont") action cont() {
    }
    @name(".rewrite_mac") action rewrite_mac(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
    }
    @name("._drop") action _drop() {
        mark_to_drop();
    }
    @name(".dec_counter") table dec_counter {
        actions = {
            decreasereg;
            cont;
        }
        key = {
            meta.meta.ndpflags: ternary;
        }
        size = 2;
    }
    @name(".send_frame") table send_frame {
        actions = {
            rewrite_mac;
            _drop;
        }
        key = {
            standard_metadata.egress_port: exact;
        }
        size = 256;
    }
    apply {
        dec_counter.apply();
        send_frame.apply();
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".buffersense") register<bit<16>>(32w4) buffersense;
    @name(".directpriohigh") action directpriohigh() {
        standard_metadata.egress_spec = 9w1;
        meta.meta.ndpflags = hdr.ndp.flags;
    }
    @name(".set_dmac") action set_dmac(bit<48> dmac) {
        hdr.ethernet.dstAddr = dmac;
        buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port);
    }
    @name("._drop") action _drop() {
        mark_to_drop();
    }
    @name(".set_nhop") action set_nhop(bit<32> nhop_ipv4, bit<9> port) {
        meta.routing_metadata.nhop_ipv4 = nhop_ipv4;
        standard_metadata.egress_port = port;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
    }
    @name(".readbuffer") action readbuffer() {
        buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port);
    }
    @name(".setpriolow") action setpriolow() {
        standard_metadata.egress_spec = 9w0;
        buffersense.read(meta.meta.register_tmp, (bit<32>)standard_metadata.egress_port);
        buffersense.write((bit<32>)standard_metadata.egress_port, (bit<16>)(meta.meta.register_tmp + 16w1));
    }
    @name(".setpriohigh") action setpriohigh() {
        truncate((bit<32>)32w54);
        hdr.ipv4.totalLen = 16w20;
        standard_metadata.egress_spec = 9w1;
    }
    @name(".directtoprio") table directtoprio {
        actions = {
            directpriohigh;
        }
        key = {
            meta.meta.register_tmp: ternary;
        }
        size = 2;
    }
    @name(".forward") table forward {
        actions = {
            set_dmac;
            _drop;
        }
        key = {
            meta.routing_metadata.nhop_ipv4: exact;
        }
        size = 512;
    }
    @name(".ipv4_lpm") table ipv4_lpm {
        actions = {
            set_nhop;
            _drop;
        }
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        size = 1024;
    }
    @name(".readbuffersense") table readbuffersense {
        actions = {
            readbuffer;
        }
        key = {
            meta.meta.register_tmp: ternary;
        }
        size = 2;
    }
    @name(".setprio") table setprio {
        actions = {
            setpriolow;
            setpriohigh;
        }
        key = {
            meta.meta.register_tmp: ternary;
        }
        size = 2;
    }
    apply {
        if (hdr.ipv4.isValid() && hdr.ipv4.ttl > 8w0) {
            ipv4_lpm.apply();
            if (hdr.ndp.isValid() && hdr.ndp.flags > 16w1) {
                directtoprio.apply();
            }
            else {
                readbuffersense.apply();
                setprio.apply();
            }
            forward.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.ndp);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

