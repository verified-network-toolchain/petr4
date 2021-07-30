/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

const bit<16> TYPE_IPV4 = 0x0800;
const bit<16> TYPE_TELEMETRY = 0x9999;
const bit<32> BLOOM_SIZE = 8;

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;

header ethernet_t {
    macAddr_t dstAddr;
    macAddr_t srcAddr;
    bit<16>   etherType;
}

header telemetry_t {
    bit<32> maxFlows;
    bit<32> maxDelay;
    bit<16> etherType;
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

struct metadata {
    /* empty */
}

struct headers {
    ethernet_t   ethernet;
    telemetry_t telemetry;
    ipv4_t ipv4;
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
	    TYPE_TELEMETRY: parse_telemetry;
            TYPE_IPV4: parse_ipv4;
            default: accept;
        }
    }

    state parse_telemetry {
	packet.extract(hdr.telemetry);
	transition select(hdr.telemetry.etherType) {
	    TYPE_IPV4: parse_ipv4;
	    default: accept;
	}
    }
    
    state parse_ipv4 {
        packet.extract(hdr.ipv4);
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

    action drop() {
        mark_to_drop(standard_metadata);
    }
    
    action ipv4_forward(macAddr_t dstAddr, egressSpec_t port) {
        standard_metadata.egress_spec = port;
        hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = dstAddr;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
    }
    
    table ipv4 {
        key = {
            hdr.ipv4.dstAddr: exact;
        }
        actions = {
            ipv4_forward;
            drop;
        }
        default_action = drop();
    }
    
    apply {
        if (hdr.ipv4.isValid()) {
            ipv4.apply();
	}
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

bit<32> max(inout bit<32> x, in bit<32> y) {
    if(x > y) {
	return x;
    }
    return y;
}      

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    register<bit<1>>(BLOOM_SIZE) r1;
    register<bit<1>>(BLOOM_SIZE) r3;
    register<bit<1>>(BLOOM_SIZE) r2;    
    register<bit<32>>(1) flows;

    apply {
	if(!hdr.telemetry.isValid()) {
	    hdr.telemetry.setValid();
	    hdr.telemetry.etherType = hdr.ethernet.etherType;
	    hdr.ethernet.etherType = TYPE_TELEMETRY;
	    hdr.telemetry.maxFlows = 0;
	    hdr.telemetry.maxDelay = 0;
	}
	if (hdr.ipv4.isValid()) {
            bit<32> idx1 = 0;
            bit<32> idx2 = 0;
            bit<32> idx3 = 0;
	    bit<1> seen1 = 0;
	    bit<1> seen2 = 0;
	    bit<1> seen3 = 0;
	    bit<32> f = 0;	    
            hash(idx1, HashAlgorithm.identity, (bit<32>)0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, BLOOM_SIZE);
            hash(idx2, HashAlgorithm.crc16, (bit<32>)0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, BLOOM_SIZE);
            hash(idx3, HashAlgorithm.csum16, (bit<32>)0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, BLOOM_SIZE);
            r1.read(seen1, idx1);
            r2.read(seen2, idx2);
            r3.read(seen3, idx3);
	    r1.write(idx1, 1);
	    r2.write(idx2, 1);
	    r3.write(idx3, 1);
	    flows.read(f,0);
	    if(seen1 == 0 || seen2 == 0 || seen3 == 0) {
		f = f + 1;
		flows.write(0, f);
	    }
	    hdr.telemetry.maxFlows = max(hdr.telemetry.maxFlows, f);
	    hdr.telemetry.maxDelay = max(hdr.telemetry.maxDelay, standard_metadata.deq_timedelta);
        }
    }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
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
	packet.emit(hdr.telemetry);
        packet.emit(hdr.ipv4);
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
