#include <core.p4>
#include <v1model.p4>

struct metadata { }
struct headers { }


struct my_struct {
  bit<8> n;
  bool b;
}

my_struct f(in bit<8> a, in bool b) {
    my_struct ans;
    ans.n = a;
    ans.b = b;
    return ans;
}

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
        my_struct s = { 42, true };
        bit<8> num = s.n; //42
        bool boo = s.b; //true

        my_struct s2 = f(42,true);
        bit<8> num2 = s2.n; //42
        bool boo2 = s2.b; //true
        packet.emit(num);
        packet.emit((bit<8>) ((bit) boo));
        packet.emit(num2);
        packet.emit((bit<8>) ((bit) boo2));
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
