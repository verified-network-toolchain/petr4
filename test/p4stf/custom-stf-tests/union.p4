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

Union f2(in bit<16> x) {
    Union tmp;
    tmp.h2 = {x};
    return tmp;
}

Union set1(in Union x) {
    Union tmp = x;
    tmp.h1.setValid();
    tmp.h1.u = 42;
    return tmp;
}

Union set2(in Union x) {
    Union tmp = x;
    tmp.h2.setValid();
    tmp.h2.v = 42;
    return tmp;
}

Union set3(in Union x) {
    Union tmp = x;
    tmp.h1.setInvalid();
    tmp.h2.setInvalid();
    return tmp;
}

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
      Union a = f1(42);
      Union b = f2(42);
      bit<8> c = a.h1.u; //42
      bool d = a.h1.isValid(); //true
      bool e = a.h2.isValid(); //false
      bit<16> f = b.h2.v; //42
      bool g = b.h1.isValid(); //false
      bool h = b.h2.isValid(); //true
      Union i = set2(a);
      Union j = set1(b);
      bit<16> k = i.h2.v; //42
      bool l = i.h1.isValid(); //false
      bool m = i.h2.isValid(); //true
      bit<8> n = j.h1.u; //42
      bool o = j.h1.isValid(); //true
      bool p = j.h2.isValid(); //false
      Union q = set3(i);
      Union r = set3(j);
      bool s = q.h1.isValid(); //false
      bool t = q.h2.isValid(); //false
      bool u = r.h1.isValid(); //false
      bool v = r.h2.isValid(); //false

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
