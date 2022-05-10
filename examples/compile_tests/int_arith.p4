
#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers {
    bool i;
 }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
      //  bool a = - (8s8) == -8s8;
      //  bool b = (8s4) != -(8s3);
      //  bool c = -(19s7) < (19s12);
      //    bool d = 18s12 > -(18s7);
      //  bool e = -(6s8) <= -(6s7);
      //  bool f = 9s7 <= 9s7;
      //  bool g = 6s8 >= 6s7;
      //  bool h = 9s7 >= 9s7; 
        
        //bool i = 8s42 == -(8s214); 
       // bool j = 8s42 == +(8s42); 
       // bool k = 8s42 == ((-8s7 + -8s3) + (8s52)); 
       // bool l = 8s42 == (-8s42) - (-8s84); 
      //  bool m = 8s42 == -8s2 * 8s3 * -8s7; 
      //  bool n = 8s42 == 8s46 & 8s59; 
      //  bool o = 8s42 == 8s34 | 8s8; 
      //  bool p = 8s42 == ~ (-8s43); 
      //  bool q = 8s42 == 8s25 ^ 8s51; 
      //  bool r = 8s42 == 8s7 |+| 8s3 |+| 8s32; 
      //  bool s = 8s42 == 8s117 |-| 8s75;
      // segfault. 
      //  bool t = 8s42 == 8s7 + 8s3 + 8s32 + 8s128 + 8s128; 
      //  bool u = 8s42 == 8s117 - 8s75 - 8s128 - 8s128;
      //  bool v = 8s127 == 8s7 |+| 8s3 |+| 8s32 |+| 8s128 |+| 8s128; 
      //  bool w = -(8s128) == 8s117 |-| 8s75 |-| 8s128 |-| 8s128; 
      //  bool x = -(8s128) == (-8s127 - 8s1) & -8s1;
        hdr.i = s; 
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { 
        packet.emit(hdr);
    }
}

//this is declaration
V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
