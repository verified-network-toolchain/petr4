#include <core.p4>
#include <v1model.p4>

struct local_metadata_t {
    bit<16> proposal;
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
    bit<32> src;
    bit<32> dst;
}

header paxos_t {
    bit<32> inst;
    bit<16> proposal;
    bit<16> vproposal;
    bit<16> acpt;
    bit<16> msgtype;
    bit<32> val;
    bit<32> fsh;
    bit<32> fsl;
    bit<32> feh;
    bit<32> fel;
    bit<32> csh;
    bit<32> csl;
    bit<32> ceh;
    bit<32> cel;
    bit<32> ash;
    bit<32> asl;
    bit<32> aeh;
    bit<32> ael;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> length_;
    bit<16> checksum;
}

struct metadata {
    @name(".local_metadata") 
    local_metadata_t local_metadata;
}

struct headers {
    @name(".ethernet") 
    ethernet_t ethernet;
    @name(".ipv4") 
    ipv4_t     ipv4;
    @name(".paxos") 
    paxos_t    paxos;
    @name(".udp") 
    udp_t      udp;
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
            8w0x11: parse_udp;
            default: accept;
        }
    }
    @name(".parse_paxos") state parse_paxos {
        packet.extract(hdr.paxos);
        transition accept;
    }
    @name(".parse_udp") state parse_udp {
        packet.extract(hdr.udp);
        transition select(hdr.udp.dstPort) {
            16w0x8888: parse_paxos;
            default: accept;
        }
    }
    @name(".start") state start {
        transition parse_ethernet;
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".acceptor_id") register<bit<16>>(32w1) acceptor_id;
    @name(".proposal_register") register<bit<16>>(32w64000) proposal_register;
    @name(".val_register") register<bit<32>>(32w64000) val_register;
    @name(".vproposal_register") register<bit<16>>(32w64000) vproposal_register;
    @name("._drop") action _drop() {
        mark_to_drop();
    }
    @name("._no_op") action _no_op() {
    }
    @name(".forward") action forward(bit<9> port) {
        _no_op();
        standard_metadata.egress_spec = port;
        _no_op();
    }
    @name(".handle_phase1a") action handle_phase1a() {
        _no_op();
        proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal);
        vproposal_register.read(hdr.paxos.vproposal, (bit<32>)hdr.paxos.inst);
        val_register.read(hdr.paxos.val, (bit<32>)hdr.paxos.inst);
        hdr.paxos.msgtype = 16w2;
        acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0);
        hdr.udp.checksum = 16w0;
        _no_op();
    }
    @name(".handle_phase2a") action handle_phase2a() {
        _no_op();
        proposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal);
        vproposal_register.write((bit<32>)hdr.paxos.inst, (bit<16>)hdr.paxos.proposal);
        val_register.write((bit<32>)hdr.paxos.inst, (bit<32>)hdr.paxos.val);
        hdr.paxos.msgtype = 16w4;
        hdr.paxos.vproposal = hdr.paxos.proposal;
        acceptor_id.read(hdr.paxos.acpt, (bit<32>)32w0);
        hdr.udp.checksum = 16w0;
        _no_op();
    }
    @name(".read_round") action read_round() {
        proposal_register.read(meta.local_metadata.proposal, (bit<32>)hdr.paxos.inst);
    }
    @name(".drop_tbl") table drop_tbl {
        actions = {
            _drop;
        }
        size = 1;
    }
    @name(".fwd_tbl") table fwd_tbl {
        actions = {
            forward;
            _drop;
        }
        key = {
            standard_metadata.ingress_port: exact;
        }
        size = 8;
    }
    @name(".paxos_tbl") table paxos_tbl {
        actions = {
            handle_phase1a;
            handle_phase2a;
            _no_op;
        }
        key = {
            hdr.paxos.msgtype: exact;
        }
        size = 8;
    }
    @name(".round_tbl") table round_tbl {
        actions = {
            read_round;
        }
        size = 1;
    }
    apply {
        if (hdr.ipv4.isValid()) {
            fwd_tbl.apply();
        }
        if (hdr.paxos.isValid()) {
            round_tbl.apply();
            if (meta.local_metadata.proposal <= hdr.paxos.proposal) {
                paxos_tbl.apply();
            }
            else {
                drop_tbl.apply();
            }
        }
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.udp);
        packet.emit(hdr.paxos);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

