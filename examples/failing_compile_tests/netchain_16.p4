#include <core.p4>
#include <v1model.p4>

struct location_t {
    bit<16> index;
}

struct my_md_t {
    bit<32> ipaddress;
    bit<16> role;
    bit<16> failed;
}

struct reply_addr_t {
    bit<32> ipv4_srcAddr;
    bit<32> ipv4_dstAddr;
}

struct sequence_md_t {
    bit<16> seq;
    bit<16> tmp;
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

header nc_hdr_t {
    bit<8>   op;
    bit<8>   sc;
    bit<16>  seq;
    bit<128> key;
    bit<128> value;
    bit<16>  vgroup;
}

header tcp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> len;
    bit<16> checksum;
}

header overlay_t {
    bit<32> swip;
}

struct metadata {
    @name(".location") 
    location_t    location;
    @name(".my_md") 
    my_md_t       my_md;
    @name(".reply_to_client_md") 
    reply_addr_t  reply_to_client_md;
    @name(".sequence_md") 
    sequence_md_t sequence_md;
}

struct headers {
    @name(".ethernet") 
    ethernet_t    ethernet;
    @name(".ipv4") 
    ipv4_t        ipv4;
    @name(".nc_hdr") 
    nc_hdr_t      nc_hdr;
    @name(".tcp") 
    tcp_t         tcp;
    @name(".udp") 
    udp_t         udp;
    @name(".overlay") 
    overlay_t[10] overlay;
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
            8w6: parse_tcp;
            8w17: parse_udp;
            default: accept;
        }
    }
    @name(".parse_nc_hdr") state parse_nc_hdr {
        packet.extract(hdr.nc_hdr);
        transition select(hdr.nc_hdr.op) {
            8w10: accept;
            8w12: accept;
            default: accept;
        }
    }
    @name(".parse_overlay") state parse_overlay {
        packet.extract(hdr.overlay.next);
        transition select(hdr.overlay.last.swip) {
            32w0: parse_nc_hdr;
            default: parse_overlay;
        }
    }
    @name(".parse_tcp") state parse_tcp {
        packet.extract(hdr.tcp);
        transition accept;
    }
    @name(".parse_udp") state parse_udp {
        packet.extract(hdr.udp);
        transition select(hdr.udp.dstPort) {
            16w8888: parse_overlay;
            16w8889: parse_overlay;
            default: accept;
        }
    }
    @name(".start") state start {
        transition parse_ethernet;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".ethernet_set_mac_act") action ethernet_set_mac_act(bit<48> smac, bit<48> dmac) {
        hdr.ethernet.srcAddr = smac;
        hdr.ethernet.dstAddr = dmac;
    }
    @name(".ethernet_set_mac") table ethernet_set_mac {
        actions = {
            ethernet_set_mac_act;
        }
        key = {
            standard_metadata.egress_port: exact;
        }
    }
    apply {
        ethernet_set_mac.apply();
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".sequence_reg") register<bit<16>>(32w4096) sequence_reg;
    @name(".value_reg") register<bit<128>>(32w4096) value_reg;
    @name(".assign_value_act") action assign_value_act() {
        sequence_reg.write((bit<32>)meta.location.index, (bit<16>)hdr.nc_hdr.seq);
        value_reg.write((bit<32>)meta.location.index, (bit<128>)hdr.nc_hdr.value);
    }
    @name(".drop_packet_act") action drop_packet_act() {
        mark_to_drop();
    }
    @name(".pop_chain_act") action pop_chain_act() {
        hdr.nc_hdr.sc = hdr.nc_hdr.sc + 8w255;
        hdr.overlay.pop_front(1);
        hdr.udp.len = hdr.udp.len + 16w65532;
        hdr.ipv4.totalLen = hdr.ipv4.totalLen + 16w65532;
    }
    @name(".failover_act") action failover_act() {
        hdr.ipv4.dstAddr = hdr.overlay[1].swip;
        pop_chain_act();
    }
    @name(".gen_reply_act") action gen_reply_act(bit<8> message_type) {
        meta.reply_to_client_md.ipv4_srcAddr = hdr.ipv4.dstAddr;
        meta.reply_to_client_md.ipv4_dstAddr = hdr.ipv4.srcAddr;
        hdr.ipv4.srcAddr = meta.reply_to_client_md.ipv4_srcAddr;
        hdr.ipv4.dstAddr = meta.reply_to_client_md.ipv4_dstAddr;
        hdr.nc_hdr.op = message_type;
        hdr.udp.dstPort = 16w8889;
    }
    @name(".failover_write_reply_act") action failover_write_reply_act() {
        gen_reply_act(8w13);
    }
    @name(".failure_recovery_act") action failure_recovery_act(bit<32> nexthop) {
        hdr.overlay[0].swip = nexthop;
        hdr.ipv4.dstAddr = nexthop;
    }
    @name(".nop") action nop() {
        ;
    }
    @name(".find_index_act") action find_index_act(bit<16> index) {
        meta.location.index = index;
    }
    @name(".get_my_address_act") action get_my_address_act(bit<32> sw_ip, bit<16> sw_role) {
        meta.my_md.ipaddress = sw_ip;
        meta.my_md.role = sw_role;
    }
    @name(".get_next_hop_act") action get_next_hop_act() {
        hdr.ipv4.dstAddr = hdr.overlay[0].swip;
    }
    @name(".get_sequence_act") action get_sequence_act() {
        sequence_reg.read(meta.sequence_md.seq, (bit<32>)meta.location.index);
    }
    @name(".set_egress") action set_egress(bit<9> egress_spec) {
        standard_metadata.egress_spec = egress_spec;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
    }
    @name(".maintain_sequence_act") action maintain_sequence_act() {
        meta.sequence_md.seq = meta.sequence_md.seq + 16w1;
        sequence_reg.write((bit<32>)meta.location.index, (bit<16>)meta.sequence_md.seq);
        sequence_reg.read(hdr.nc_hdr.seq, (bit<32>)meta.location.index);
    }
    @name(".read_value_act") action read_value_act() {
        value_reg.read(hdr.nc_hdr.value, (bit<32>)meta.location.index);
    }
    @name(".assign_value") table assign_value {
        actions = {
            assign_value_act;
        }
    }
    @name(".drop_packet") table drop_packet {
        actions = {
            drop_packet_act;
        }
    }
    @name(".failure_recovery") table failure_recovery {
        actions = {
            failover_act;
            failover_write_reply_act;
            failure_recovery_act;
            nop;
            drop_packet_act;
        }
        key = {
            hdr.ipv4.dstAddr   : ternary;
            hdr.overlay[1].swip: ternary;
            hdr.nc_hdr.vgroup  : ternary;
        }
    }
    @name(".find_index") table find_index {
        actions = {
            find_index_act;
        }
        key = {
            hdr.nc_hdr.key: exact;
        }
    }
    @name(".gen_reply") table gen_reply {
        actions = {
            gen_reply_act;
        }
        key = {
            hdr.nc_hdr.op: exact;
        }
    }
    @name(".get_my_address") table get_my_address {
        actions = {
            get_my_address_act;
        }
        key = {
            hdr.nc_hdr.key: exact;
        }
    }
    @name(".get_next_hop") table get_next_hop {
        actions = {
            get_next_hop_act;
        }
    }
    @name(".get_sequence") table get_sequence {
        actions = {
            get_sequence_act;
        }
    }
    @stage(11) @name(".ipv4_route") table ipv4_route {
        actions = {
            set_egress;
        }
        key = {
            hdr.ipv4.dstAddr: exact;
        }
        size = 8192;
    }
    @name(".maintain_sequence") table maintain_sequence {
        actions = {
            maintain_sequence_act;
        }
    }
    @name(".pop_chain") table pop_chain {
        actions = {
            pop_chain_act;
        }
    }
    @name(".pop_chain_again") table pop_chain_again {
        actions = {
            pop_chain_act;
        }
    }
    @name(".read_value") table read_value {
        actions = {
            read_value_act;
        }
    }
    apply {
        if (hdr.nc_hdr.isValid()) {
            get_my_address.apply();
            if (hdr.ipv4.dstAddr == meta.my_md.ipaddress) {
                find_index.apply();
                get_sequence.apply();
                if (hdr.nc_hdr.op == 8w10) {
                    read_value.apply();
                }
                else {
                    if (hdr.nc_hdr.op == 8w12) {
                        if (meta.my_md.role == 16w100) {
                            maintain_sequence.apply();
                        }
                        if (meta.my_md.role == 16w100 || hdr.nc_hdr.seq > meta.sequence_md.seq) {
                            assign_value.apply();
                            pop_chain.apply();
                        }
                        else {
                            drop_packet.apply();
                        }
                    }
                }
                if (meta.my_md.role == 16w102) {
                    pop_chain_again.apply();
                    gen_reply.apply();
                }
                else {
                    get_next_hop.apply();
                }
            }
        }
        if (hdr.nc_hdr.isValid()) {
            failure_recovery.apply();
        }
        if (hdr.tcp.isValid() || hdr.udp.isValid()) {
            ipv4_route.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.udp);
        packet.emit(hdr.overlay);
        packet.emit(hdr.nc_hdr);
        packet.emit(hdr.tcp);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
        update_checksum_with_payload(true, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, 8w0, hdr.ipv4.protocol, hdr.udp.len, hdr.udp.srcPort, hdr.udp.dstPort, hdr.udp.len }, hdr.udp.checksum, HashAlgorithm.csum16);
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

