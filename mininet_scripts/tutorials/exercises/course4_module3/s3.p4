/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;

const bit<16> TYPE_IPV4 = 0x800;
const bit<16> TYPE_DISCOVERY = 0x2A2A;
const bit<8>  PROTO_TCP = 6;
const bit<9> CTRL_PT = 9w510;
const bit<8> UNINIT = 0xFF;

const bit<9> IN = 1;
const bit<9> OUT = 6;
const ip4Addr_t VIP = 3232235521; //192.168.0.1
const int MAX_SERVER_CNT = 4;
const int LSB = 6;

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

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

header discovery_hdr_t {
    bit<8> start_id;
    bit<8> start_pt;
    bit<8> end_pt;
}

struct metadata {
    /* empty */
    bit<32> server_id;
    bit<32> active_server_cnt;
}

struct headers {
    ethernet_t      ethernet;
    ipv4_t          ipv4;
    tcp_t           tcp;
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
        transition select(hdr.ipv4.protocol){
          PROTO_TCP: parse_tcp;
          default: accept;
        }
    }

    state parse_tcp{
        packet.extract(hdr.tcp);
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
    action drop() {
        mark_to_drop(standard_metadata);
    }

    register<bit<32>>(MAX_SERVER_CNT) server_load;
    register<bit<51>>(1024) conns;

    action do_lb(){
        // create hash input
        // compute the index
        bit<10> index;
        hash(index, HashAlgorithm.crc16, (bit<32>)0, {hdr.ipv4.srcAddr, hdr.tcp.srcPort}, (bit<32>)1024);
        // read connection info
        bit<51> conn;
        conns.read(conn, (bit<32>)index);

        bit<32> min_load;
        
        if (conn[50:50] == 1w1){
            if (conn[49:18] == hdr.ipv4.srcAddr &&
                conn[17:2] == hdr.tcp.srcPort){
              meta.server_id[31:2] = 30w0;
              meta.server_id[1:0] = conn[1:0];

              server_load.read(min_load, meta.server_id);
              min_load = min_load + 1;
              server_load.write(meta.server_id, min_load);   
            }
            else {
              drop();
            } 
        } 

        else {
          meta.server_id = 32w0; 
          server_load.read(min_load, 32w0);

          
          bit<32> comp;

          if (meta.active_server_cnt > 1){
            server_load.read(comp, 32w1);
            if (comp[31:LSB] < min_load[31:LSB]){
              min_load = comp;
              meta.server_id = 32w1;
            }
            
            if (meta.active_server_cnt > 2){ 
              server_load.read(comp, 32w2);
              if (comp[31:LSB] < min_load[31:LSB]){
                min_load = comp;
                meta.server_id = 32w2;
              }

              if (meta.active_server_cnt > 3){
                server_load.read(comp, 32w3);
                if (comp[31:LSB] < min_load[31:LSB]){
                  min_load = comp;
                  meta.server_id = 32w3;
                }
              }
            }
          }
         
          min_load = min_load + 1;
          server_load.write(meta.server_id, min_load); 

          conn[50:50] = 1w1;
          conn[49:18] = hdr.ipv4.srcAddr;
          conn[17:2] = hdr.tcp.srcPort;
          conn[1:0] = meta.server_id[1:0];

          conns.write((bit<32>)index, conn);
          
       }
    }

    action fw(ip4Addr_t addr, egressSpec_t port){
        hdr.ipv4.dstAddr = addr;
        standard_metadata.egress_spec = port;
    }

    table set_dst {
      key = {
        meta.server_id: exact;
      }

      actions = {
        fw;
        drop;
        NoAction;
      }
      default_action = drop();
    }

    action set_vip(ip4Addr_t addr){
        hdr.ipv4.srcAddr = addr;
    }

    table set_src {
        key = {
          hdr.ipv4.srcAddr: exact;
        }

        actions = {
          set_vip;
          NoAction;
        }
        default_action = NoAction;
    }
               
    apply {
        if (hdr.ipv4.isValid()) {
          if (standard_metadata.ingress_port == IN){
              do_lb();
              // set dstip based on server id
              set_dst.apply();
          }
          else if (standard_metadata.ingress_port != OUT){
              set_src.apply();
              standard_metadata.egress_spec = OUT;
          }
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

        update_checksum_with_payload(hdr.tcp.isValid(),
                                   {hdr.ipv4.srcAddr,
                                    hdr.ipv4.dstAddr,
                                    8w0,
                                    hdr.ipv4.protocol,
                                    (bit<16>)(hdr.ipv4.totalLen - 20),
                                    hdr.tcp.srcPort,
                                    hdr.tcp.dstPort,
                                    hdr.tcp.seqNo,
                                    hdr.tcp.ackNo,
                                    hdr.tcp.dataOffset,
                                    hdr.tcp.res,
                                    hdr.tcp.ecn,
                                    hdr.tcp.ctrl,
                                    hdr.tcp.window,
                                    16w0,
                                    hdr.tcp.urgentPtr},
                                    hdr.tcp.checksum,
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
        packet.emit(hdr.tcp);
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
