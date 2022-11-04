/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

#define TYPE_IPV4 16w0x800
#define TYPE_HULA 16w0x2345

#define MAX_HOPS  9
#define TOR_NUM   32
#define TOR_NUM_1 33

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;
typedef bit<15> qdepth_t;
typedef bit<32> digest_t;

header ethernet_t {
    macAddr_t dstAddr;
    macAddr_t srcAddr;
    bit<16>   etherType;
}

header srcRoute_t {
    bit<1>    bos;
    bit<15>   port;
}

header hula_t {
    /* 0 is forward path, 1 is the backward path */
    bit<1>   dir;
    /* max qdepth seen so far in the forward path */
    qdepth_t qdepth;
    /* digest of the source routing list to uniquely identify each path */
    digest_t digest;
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
    ip4Addr_t srcAddr;
    ip4Addr_t dstAddr;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> length_;
    bit<16> checksum;
}

struct metadata {
    /* At destination ToR, this is the index of register 
       that saves qdepth for the best path from each source ToR */
    bit<32> index;
}

struct headers {
    ethernet_t              ethernet;
    srcRoute_t[9]    srcRoutes;
    ipv4_t                  ipv4;
    udp_t                   udp;
    hula_t                  hula;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

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
            TYPE_HULA : parse_hula;
            TYPE_IPV4 : parse_ipv4;
            default   : accept;
        }
    }

    state parse_hula {
        packet.extract(hdr.hula);
        transition parse_srcRouting;
    }

    state parse_srcRouting {
        packet.extract(hdr.srcRoutes.next);
        transition select(hdr.srcRoutes.last.bos) {
            1w1       : parse_ipv4;
            default : parse_srcRouting;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            8w17: parse_udp;
            default: accept;
        }
    }

    state parse_udp {
        packet.extract(hdr.udp);
        transition accept;
    }

}


/*************************************************************************
************   C H E C K S U M    V E R I F I C A T I O N   *************
*************************************************************************/

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {   
    apply {  }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    /* 
     * At destination ToR, saves the queue depth of the best path from
     * each source ToR
     */
    register<qdepth_t>(32w32) srcindex_qdepth_reg;

    /* 
     * At destination ToR, saves the digest of the best path from
     * each source ToR
     */
    register<digest_t>(32w32) srcindex_digest_reg;

    /* At each hop, saves the next hop to reach each destination ToR */
    register<bit<16>>(32w32) dstindex_nhop_reg;

    /* At each hop saves the next hop for each flow */
    register<bit<16>>(32w65536) flow_port_reg;

    /* This action will drop packets */
    action drop() {
        mark_to_drop();
    }

    action nop() {
    }

    action update_ttl(){
        hdr.ipv4.ttl = hdr.ipv4.ttl - 8w1;
    }

    action set_dmac(macAddr_t dstAddr){
        hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = dstAddr;
    }
    
    /* This action just applies source routing */
    action srcRoute_nhop() {
        standard_metadata.egress_spec = (bit<9>)hdr.srcRoutes[0].port;
        hdr.srcRoutes.pop_front(1);
    }

    /* 
     * Runs if it is the destination ToR.
     * Control plane Gives the index of register for best path from source ToR
     */
    action hula_dst(bit<32> index) {
        meta.index = index;
    }

    /* 
     * In reverse path, update nexthop to a destination ToR to ingress port
     * where we receive hula packet
     */
    action hula_set_nhop(bit<32> index) {
        dstindex_nhop_reg.write(index, (bit<16>)standard_metadata.ingress_port); 
    }

    /* Read next hop that is saved in hula_set_nhop action for data packets */
    action hula_get_nhop(bit<32> index){
       bit<16> tmp;
       dstindex_nhop_reg.read(tmp, index); 
       standard_metadata.egress_spec = (bit<9>)tmp;
    }

    /* Record best path at destination ToR */
    action change_best_path_at_dst(){
        srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth);
        srcindex_digest_reg.write(meta.index, hdr.hula.digest);
    }

    /* 
     * At destination ToR, return packet to source by
     * - changing its hula direction
     * - send it to the port it came from
     */
    action return_hula_to_src(){
        hdr.hula.dir = 1w1;
        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }

    /* 
     * In forward path:
     * - if destination ToR: run hula_dst to set the index based on srcAddr
     * - otherwise run srcRoute_nhop to perform source routing
     */
    table hula_fwd {
        key = {
            hdr.ipv4.dstAddr: exact;
            hdr.ipv4.srcAddr: exact;
        }
        actions = {
            hula_dst;
            srcRoute_nhop;
        }
        default_action = srcRoute_nhop;
        size = 33; // TOR_NUM + 1
    }

    /* 
     * At each hop in reverse path
     * update next hop to destination ToR in registers.
     * index is set based on dstAddr
     */
    table hula_bwd {
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        actions = {
            hula_set_nhop;
        }
        size = TOR_NUM;
    }

    /* 
     * in reverse path: 
     * - if source ToR (srcAddr = this switch) drop hula packet 
     * - otherwise, just forward in the reverse path based on source routing
     */
    table hula_src {
        key = {
            hdr.ipv4.srcAddr: exact;
        }
        actions = {
            drop;
            srcRoute_nhop;
        }
        default_action = srcRoute_nhop;
        size = 2;
    }

    /*
     * get nexthop based on dstAddr using registers
     */
    table hula_nhop {
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        actions = {
            hula_get_nhop;
            drop;
        }
        default_action = drop;
        size = TOR_NUM;
    }

    /*
     * set right dmac for packets going to hosts
     */
    table dmac {
        key = {
            standard_metadata.egress_spec : exact;
        }
        actions = {
            set_dmac;
            nop;
        }
        default_action = nop;
        size = 16;
    }

    apply {
        if (hdr.hula.isValid()){
            if (hdr.hula.dir == 1w0){
                switch(hula_fwd.apply().action_run){

                    /* if hula_dst action ran, this is the destination ToR */
                    hula_dst: {

                        /* if it is the destination ToR compare qdepth */
                        qdepth_t old_qdepth;
                        srcindex_qdepth_reg.read(old_qdepth, meta.index);

                        if (old_qdepth > hdr.hula.qdepth){
                            change_best_path_at_dst();

                            /* only return hula packets that update best path */
                            return_hula_to_src();
                        }else{

                            /* update the best path even if it has gone worse 
                             * so that other paths can replace it later
                             */
                            digest_t old_digest;
                            srcindex_digest_reg.read(old_digest, meta.index);
                            if (old_digest == hdr.hula.digest){
                                srcindex_qdepth_reg.write(meta.index, hdr.hula.qdepth);
                            }

                            drop();
                        } 
                    }
                }
            }else {
                /* update routing table in reverse path */
                hula_bwd.apply();

                /* drop if source ToR */
                hula_src.apply();
            }

        }else if (hdr.ipv4.isValid()){
            bit<16> flow_hash;
            hash(
                flow_hash, 
                HashAlgorithm.crc16, 
                16w0, 
                { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.udp.srcPort}, 
                32w65536);

            /* look into hula tables */
            bit<16> port;
            flow_port_reg.read(port, (bit<32>)flow_hash);

            if (port == 16w0){
                /* if it is a new flow check hula paths */
                hula_nhop.apply();
                flow_port_reg.write((bit<32>)flow_hash, (bit<16>)standard_metadata.egress_spec);
            }else{
                /* old flows still use old path to avoid oscilation and packet reordering */
                standard_metadata.egress_spec = (bit<9>)port;
            }

            /* set the right dmac so that ping and iperf work */
            dmac.apply();
        }else {
            drop();
        }

        if (hdr.ipv4.isValid()){
            update_ttl();
        }
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {
        if (hdr.hula.isValid() && hdr.hula.dir == 1w0){

            /* pick max qdepth in hula forward path */
            if (hdr.hula.qdepth < (qdepth_t)standard_metadata.deq_qdepth){

                /* update queue length */
                hdr.hula.qdepth = (qdepth_t)standard_metadata.deq_qdepth;
            } 
        }
    }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
     apply {
	update_checksum(
	    hdr.ipv4.isValid(),
            { hdr.ipv4.version,
	      hdr.ipv4.ihl,
              hdr.ipv4.diffserv,
              hdr.ipv4.totalLen,
              hdr.ipv4.identification,
              hdr.ipv4.flags,
              hdr.ipv4.fragOffset,
              hdr.ipv4.ttl,
              hdr.ipv4.protocol,
              hdr.ipv4.srcAddr,
              hdr.ipv4.dstAddr },
            hdr.ipv4.hdrChecksum,
            HashAlgorithm.csum16);
    }
}

/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.hula);
        packet.emit(hdr.srcRoutes);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.udp);
    }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;
