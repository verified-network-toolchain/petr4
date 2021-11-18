/*******************************************************************************
 * 
 ******************************************************************************/

#include <core.p4>
#if __TARGET_TOFINO__ == 2
#include <t2na.p4>
#else
#include <tna.p4>
#endif

#include "common/headers.p4"
#include "common/util.p4"

const PortId_t INCOMING = 9w0;
const PortId_t OUTGOING = 9w1;

typedef bit<16> reg_index_t;
typedef bit<1> reg_value_t;
typedef bit<64> ip_pair_t;
#define REG_LEN 32w65536

struct metadata_t {
    ip_pair_t key;
    bit<16> ind_0;
    bit<16> ind_1;
    bit<1> rw_0;
    bit<1> rw_1;
    bit<1> matched;
}

// ---------------------------------------------------------------------------
// Ingress parser
// ---------------------------------------------------------------------------

parser EtherIPTCPUDPParser(
        packet_in pkt,
        out header_t hdr) {
    state start {
        transition parse_ethernet;
    }
    state parse_ethernet {
        pkt.extract(hdr.ethernet);
        transition select (hdr.ethernet.ether_type) {
            ETHERTYPE_IPV4 : parse_ipv4;
            default : reject;
        }
    }
    state parse_ipv4 {
        pkt.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            IP_PROTOCOLS_TCP : parse_tcp;
            IP_PROTOCOLS_UDP : parse_udp;
            default : accept;
        }
    }
    state parse_tcp {
        pkt.extract(hdr.tcp);
        transition accept;
    }
    state parse_udp {
        pkt.extract(hdr.udp);
        transition accept;
    }  
}

parser SwitchIngressParser(
        packet_in pkt,
        out header_t hdr,
        out metadata_t ig_md,
        out ingress_intrinsic_metadata_t ig_intr_md) {

    TofinoIngressParser() tofino_parser;
    EtherIPTCPUDPParser() layer4_parser;

    state start {
        tofino_parser.apply(pkt, ig_intr_md);
        layer4_parser.apply(pkt, hdr);
        transition accept;
    }
}


// ---------------------------------------------------------------------------
// Ingress
// ---------------------------------------------------------------------------
control SwitchIngress(
        inout header_t hdr,
        inout metadata_t ig_md,
        in ingress_intrinsic_metadata_t ig_intr_md,
        in ingress_intrinsic_metadata_from_parser_t ig_intr_prsr_md,
        inout ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md,
        inout ingress_intrinsic_metadata_for_tm_t ig_intr_tm_md) {

    // Hash index 0
    CRCPolynomial<bit<16>>(16w0x3D65,false,false,false,0,0) crc_poly_0;
    Hash<bit<16>>(HashAlgorithm_t.CRC16, crc_poly_0) crc16_0;
    action hash_0() {
        ig_md.ind_0 = crc16_0.get({ig_md.key});
    }
    
    action get_key_0_outgoing() {
        ig_md.key = hdr.ipv4.src_addr ++ hdr.ipv4.dst_addr;
    }
    
    action get_key_0_incoming() {
        ig_md.key = hdr.ipv4.dst_addr ++ hdr.ipv4.src_addr;
    }

    table get_key_0 {
        key = {
            ig_intr_md.ingress_port: exact;
        }
        actions = {
            get_key_0_outgoing;
            get_key_0_incoming;
        }
        const entries = {
            (OUTGOING) : get_key_0_outgoing();
            (INCOMING) : get_key_0_incoming();
        }
        size = 2;
    }

    // Bloom row 0
    Register<reg_value_t, reg_index_t>(REG_LEN, 0) reg_0;
    
    RegisterAction<reg_value_t, reg_index_t, reg_value_t>(reg_0) insert_0 = {
        void apply(inout reg_value_t value, out reg_value_t rv) {
            value = 1;
            rv = value;
        }
    };
    
    RegisterAction<reg_value_t, reg_index_t, reg_value_t>(reg_0) query_0 = {
        void apply(inout reg_value_t value, out reg_value_t rv) {
            rv = value;
        }
    };
    
    action insert_action_0() {
        ig_md.rw_0=insert_0.execute(ig_md.ind_0);
    }

    action query_action_0() {
        ig_md.rw_0=query_0.execute(ig_md.ind_0);
    }

    table bloom_0 {
        key = {
            ig_intr_md.ingress_port: exact;
        }
        actions = {
            insert_action_0;
            query_action_0;
        }
        const entries = {
            (OUTGOING) : insert_action_0();
            (INCOMING) : query_action_0();
        }
        size = 2;
    }
    
    apply {
        get_key_0.apply();
        hash_0();
        bloom_0.apply();
    }
}

// ---------------------------------------------------------------------------
// Ingress Deparser
// ---------------------------------------------------------------------------
control SwitchIngressDeparser(
        packet_out pkt,
        inout header_t hdr,
        in metadata_t ig_md,
        in ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md) {

    apply {
        pkt.emit(hdr);
    }
}

// ---------------------------------------------------------------------------
// Egress Parser
// ---------------------------------------------------------------------------
parser SwitchEgressParser(
        packet_in pkt,
        out header_t hdr,
        out metadata_t eg_md,
        out egress_intrinsic_metadata_t eg_intr_md) {

    TofinoEgressParser() tofino_parser;
    EtherIPTCPUDPParser() layer4_parser;

    state start {
        tofino_parser.apply(pkt, eg_intr_md);
        layer4_parser.apply(pkt, hdr);
        transition accept;
    }
}


// ---------------------------------------------------------------------------
// Egress 
// ---------------------------------------------------------------------------
control SwitchEgress(
        inout header_t hdr,
        inout metadata_t eg_md,
        in egress_intrinsic_metadata_t eg_intr_md,
        in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr,
        inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
        inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport) {

    apply {
        // empty
    }
}

// ---------------------------------------------------------------------------
// Egress Deparser
// ---------------------------------------------------------------------------
control SwitchEgressDeparser(packet_out pkt,
                              inout header_t hdr,
                              in metadata_t eg_md,
                              in egress_intrinsic_metadata_for_deparser_t 
                                eg_intr_dprsr_md
                              ) {
    apply {
        pkt.emit(hdr);
    }
}


Pipeline(SwitchIngressParser(),
         SwitchIngress(),
         SwitchIngressDeparser(),
         SwitchEgressParser(),
         SwitchEgress(),
         SwitchEgressDeparser()) pipe;

Switch(pipe) main;
