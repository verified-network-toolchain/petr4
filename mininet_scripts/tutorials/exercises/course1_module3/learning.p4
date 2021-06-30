/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

const bit<9> CTRL_PT = 9w510;
const bit<16> TYPE_BCAST = 0x8888;

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

header bcast_t {
    bit<16> etherType;
}

struct metadata {
    /* empty */
}

struct headers {
    ethernet_t   ethernet;
    bcast_t      bcast;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
	    TYPE_BCAST: parse_bcast;
	    default: accept;
	}
    }

    state parse_bcast {
    	packet.extract(hdr.bcast);
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

    action forward(bit<9> port) {
	standard_metadata.egress_spec = (bit<9>) port;
    }

    action punt() {
        forward(CTRL_PT);
    }

    table ethernet_learning {
        key = {
	    hdr.ethernet.dstAddr:exact;
	    hdr.ethernet.srcAddr:exact;
	}
	actions = {
	    forward;
	    punt;
	}
	default_action = punt();
    }
    
    apply {
       if (hdr.ethernet.dstAddr == 0xffffffffffff || hdr.ethernet.etherType == TYPE_BCAST) {
         standard_metadata.mcast_grp = 1;
       } else {
         ethernet_learning.apply();
       }       
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout metadata meta,
    inout standard_metadata_t standard_metadata) {

    action drop() {
	mark_to_drop(standard_metadata);
    }

    action pass() { }   

    table spanning_tree {
	key = {
          standard_metadata.egress_port: exact;
	}

	actions = {
	    drop;
	    pass;
	}
	
	default_action = drop();
    }
    
    apply {
      if(hdr.ethernet.dstAddr == 0xffffffffffff || hdr.ethernet.etherType == TYPE_BCAST) {
        spanning_tree.apply();
      }
      if(hdr.ethernet.etherType == TYPE_BCAST) {
        hdr.ethernet.etherType = hdr.bcast.etherType;
	hdr.bcast.setInvalid();
      }
    }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
     apply {  }
}

/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
	packet.emit(hdr.bcast);
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
