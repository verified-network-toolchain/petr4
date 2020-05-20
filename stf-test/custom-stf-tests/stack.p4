#include <core.p4>
#include <v1model.p4>

header MyHeader {
    bit<8> a;
    bit<8> b;
}

MyHeader[5] init() {
    MyHeader[5] tmp;
    return tmp;
}

MyHeader[5] set_next(in MyHeader[5] a) {
    MyHeader[5] tmp = a;
    tmp.next = {42,42};
    return tmp;
}

MyHeader[5] set_third(in MyHeader[5] a) {
    MyHeader[5] tmp = a;
    tmp[3] = {42,42};
    return tmp;
}

MyHeader[5] push1(in MyHeader[5] a) {
    a.push_front(1);
    return a;
}

MyHeader[5] pop2(in MyHeader[5] a) {
    a.pop_front(2);
    return a;
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
      MyHeader[5] a = init();
      MyHeader b = a[0];
      MyHeader c = a[1];
      MyHeader d = a[2];
      MyHeader e = a[3];
      MyHeader f = a[4];
      bit<32> g = a.size; //5
      MyHeader h = a.next;
      MyHeader[5] i = set_next(a);
      MyHeader j = i.next;
      MyHeader[5] k = set_third(i);
      MyHeader l = k[3];
      MyHeader[5] m = push1(k);
      MyHeader n = m[0];
      MyHeader o = m[1];
      MyHeader p = m[2];
      MyHeader q = m[3];
      MyHeader r = m[4];
      MyHeader[5] s = pop2(m);
      MyHeader t = s[0];
      MyHeader u = s[1];
      MyHeader v = s[2];
      MyHeader w = s[3];
      MyHeader x = s[4];
      packet.emit(b);
      packet.emit(c);
      packet.emit(d);
      packet.emit(e);
      packet.emit(f);
      packet.emit(g);
      packet.emit(h);
      packet.emit(j);
      packet.emit(l);
      packet.emit(n);
      packet.emit(o);
      packet.emit(p);
      packet.emit(q);
      packet.emit(r);
      packet.emit(t);
      packet.emit(u);
      packet.emit(v);
      packet.emit(w);
      packet.emit(x);
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
