#include <core.p4>
#include <v1model.p4>

header H1 {
  bit<8> u;
}

header H2  {
  bit<16> v;
}

header_union Union {
  H1 h1;
  H2 h2;
}

Union f1(in bit<8> x) {
    Union tmp;
    tmp.h1 = {x};
    return tmp;
}

Union f2(in bit<8> x) {
    Union tmp;
    tmp.h2 = {x};
    return tmp;
}

Union set1(in Union x) {
    x.h1.setValid();
    x.h1.u = 42;
    return x;
}

Union set2(in Union x) {
    x.h2.setValid();
    x.h2.v = 42;
    return x;
}

Union set3(in Union x) {
    x.h1.setInvalid();
    x.h2.setInvalid();
    return x;
}

const Union a = f1(42);
const Union b = f2(42);
const bit<8> c = a.h1.u; //42
const bool d = a.h1.isValid(); //true
const bool e = a.h2.isValid(); //false
const bit<16> f = b.h2.v; //42
const bool g = b.h1.isValid(); //false
const bool h = b.h2.isValid(); //true
const Union i = set2(a);
const Union j = set1(b);
const bit<16> k = i.h2.v; //42
const bool l = i.h1.isValid(); //false
const bool m = i.h2.isValid(); //true
const bit<8> n = j.h1.u; //42
const bool o = j.h1.isValid(); //true
const bool p = j.h2.isValid(); //false
const Union q = set3(i);
const Union r = set3(j);
const bool s = q.h1.isValid(); //false
const bool t = q.h2.isValid(); //false
const bool u = r.h1.isValid(); //false
const bool v = r.h2.isValid(); //false

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
      packet.emit(c);
      packet.emit((bit<8>) ((bit) d));
      packet.emit((bit<8>) ((bit) e));
      packet.emit(f);
      packet.emit((bit<8>) ((bit) g));
      packet.emit((bit<8>) ((bit) h));
      packet.emit(k);
      packet.emit((bit<8>) ((bit) l));
      packet.emit((bit<8>) ((bit) m));
      packet.emit(n);
      packet.emit((bit<8>) ((bit) o));
      packet.emit((bit<8>) ((bit) p));
      packet.emit((bit<8>) ((bit) s));
      packet.emit((bit<8>) ((bit) t));
      packet.emit((bit<8>) ((bit) u));
      packet.emit((bit<8>) ((bit) v));
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
