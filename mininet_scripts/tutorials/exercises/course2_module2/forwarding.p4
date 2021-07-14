/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

const bit<16> TYPE_IPV4 = 0x800;
const bit<16> TYPE_DISCOVERY = 0x2A2A;
const bit<9> CTRL_PT = 9w510;
const bit<8> UNINIT = 0xFF;

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;

typedef bit<1> bool_t;
typedef bit<8> port_ind_t;
typedef bit<8> weight_t;
typedef bit<4> demand_id_t;

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

header discovery_hdr_t {
    bit<8> start_id;
    bit<8> start_pt;
    bit<8> end_pt;
}

header port_info_t{
  egressSpec_t port;
  weight_t weight;
}

struct metadata {
  port_info_t[5] port_info;
}

struct headers {
    ethernet_t      ethernet;
    ipv4_t          ipv4;
    discovery_hdr_t discovery;
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
            TYPE_IPV4: parse_ipv4;
	    TYPE_DISCOVERY: parse_discovery;
            default: accept;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition accept;
    }

    state parse_discovery {
	packet.extract(hdr.discovery);
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
    counter (6, CounterType.packets) port_cntr;
    // register keeps val, cur_port_ind, cur_weight_counter
    register<bit<17>>(16) cur_path;

    action drop() {
        mark_to_drop(standard_metadata);
    }
    
    action ipv4_forward(demand_id_t demand_id, macAddr_t dstAddr, 
                        port_ind_t valid_ports,
                        egressSpec_t port1, weight_t weight1,
                        egressSpec_t port2, weight_t weight2,
                        egressSpec_t port3, weight_t weight3,
                        egressSpec_t port4, weight_t weight4,
                        egressSpec_t port5, weight_t weight5) {

        hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = dstAddr;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 1;

        meta.port_info[0] = {port = port1, weight = weight1};
        meta.port_info[1] = {port = port2, weight = weight2};
        meta.port_info[2] = {port = port3, weight = weight3};
        meta.port_info[3] = {port = port4, weight = weight4};
        meta.port_info[4] = {port = port5, weight = weight5};

        bit<17> reg_val;
        cur_path.read(reg_val, (bit<32>)demand_id);
        bool_t val = reg_val[16:16];
        port_ind_t port_ind = reg_val[15:8];
        weight_t weight_cntr = reg_val[7:0]; 

        if (val == 1){
          weight_t max_weight = meta.port_info[(bit<8>)port_ind].weight;
          if (weight_cntr >= max_weight){
            weight_cntr = 1;
            port_ind = port_ind + 1;
            if (port_ind == valid_ports){
              port_ind = 0;
            }
          }
          else {
            weight_cntr = weight_cntr + 1;
          } 
        }
        else {
          val = 1;
          port_ind = 0;
          weight_cntr = 1; 
        }
       
        reg_val[16:16] = val;
        reg_val[15:8] = port_ind;
        reg_val[7:0] = weight_cntr;

        standard_metadata.egress_spec = meta.port_info[(bit<8>)port_ind].port; 
    }
    
    table ipv4 {
        key = {
            hdr.ipv4.srcAddr: exact;
            hdr.ipv4.dstAddr: exact;
        }
        actions = {
            ipv4_forward;
            drop;
            NoAction;
        }
        default_action = drop();
    }

        
    apply {
        if (hdr.ipv4.isValid()) {
	        ipv4.apply();
          port_cntr.count((bit<32>)standard_metadata.egress_spec); 
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
	if (hdr.discovery.isValid() && hdr.discovery.start_pt == UNINIT) {
	    hdr.discovery.start_pt = (bit<8>) standard_metadata.egress_port;
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
        packet.emit(hdr.ipv4);
	packet.emit(hdr.discovery);
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
