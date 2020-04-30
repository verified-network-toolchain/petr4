#include <core.p4>
#include <v1model.p4>

header my_header {
  bit<2> first;
  bit<2> second;
}

my_header f(in bit<2> a, in bit<2> b) {
    my_header ans;
    ans.setValid();
    ans.first = a;
    ans.second = b;
    return ans;
}

my_header g(in my_header hdr) {
    hdr.setInvalid();
    return hdr;
}

const my_header head = { 1, 0 };
const bool a = head.isValid(); //true; initializing with a list expression makes it valid
const bit<2> b = head.first; // 1
const bit<2> c = head.second; // 0

const my_header head2 = g(head);
const bool d = head2.isValid(); //false
const bit<2> e = head2.first; //1
const bit<2> h = head2.second;//0

const my_header head3 = f(2,3);
const bool i = head3.isValid(); //true
const bit<2> j = head3.first; //2
const bit<2> k = head3.second; //3

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
        packet.emit((bit<8>) ((bit) a));
        packet.emit((bit<8>) b);
        packet.emit((bit<8>) c);
        packet.emit((bit<8>) ((bit) d));
        packet.emit((bit<8>) e);
        packet.emit((bit<8>) h);
        packet.emit((bit<8>) ((bit) i));
        packet.emit((bit<8>) j);
        packet.emit((bit<8>) k);

    }
}

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    ) main;
