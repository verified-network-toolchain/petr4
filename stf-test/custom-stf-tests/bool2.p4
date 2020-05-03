#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { 
      bool a = true;
      bool b = false;
      bool c = true && true;
      bool d = true && false;
      bool e = false && true;
      bool f = false && false;
      bool g = true || true;
      bool h = true || false;
      bool i = false || true;
      bool j = false || false;
      bool k = !true;
      bool l = !false;
      bool m = true == true;
      bool n = false == false;
      bool o = false == true;
      bool p = true == false;
      bool q = true != true;
      bool r = true != false;
      bool s = false != true;
      bool t = false != false;
      bit<1> u = true ? 1w1 : 1w0;
      bit<1> v = false ? 1w1 : 1w0;
      packet.emit((bit<8>) ((bit) a));
      packet.emit((bit<8>) ((bit) b));
      packet.emit((bit<8>) ((bit) c));
      packet.emit((bit<8>) ((bit) d));
      packet.emit((bit<8>) ((bit) e));
      packet.emit((bit<8>) ((bit) f));
      packet.emit((bit<8>) ((bit) g));
      packet.emit((bit<8>) ((bit) h));
      packet.emit((bit<8>) ((bit) i));
      packet.emit((bit<8>) ((bit) j));
      packet.emit((bit<8>) ((bit) k));
      // packet.emit((bit<8>) ((bit) l));
      // packet.emit((bit<8>) ((bit) m));
      // packet.emit((bit<8>) ((bit) n));
      // packet.emit((bit<8>) ((bit) o));
      // packet.emit((bit<8>) ((bit) p));
      // packet.emit((bit<8>) ((bit) q));
      // packet.emit((bit<8>) ((bit) r));
      // packet.emit((bit<8>) ((bit) s));
      // packet.emit((bit<8>) ((bit) t));
      // packet.emit((bit<8>) u);
      // packet.emit((bit<8>) v);
    }
}

//this is declaration
V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    ) main;
