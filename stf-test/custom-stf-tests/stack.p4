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
struct headers {
    MyHeader[5] a;
    MyHeader b;
    MyHeader c;
    MyHeader d;
    MyHeader e;
    MyHeader f;
    bit<32> g;
    MyHeader h;
    MyHeader[5] i;
    MyHeader j;
    MyHeader[5] k;
    MyHeader l;
    MyHeader[5] m;
    MyHeader n;
    MyHeader o;
    MyHeader p;
    MyHeader q;
    MyHeader r;
    MyHeader[5] s;
    MyHeader t;
    MyHeader u;
    MyHeader v;
    MyHeader w;
    MyHeader x;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        hdr.a = init();
        hdr.b = hdr.a[0];
        hdr.c = hdr.a[1];
        hdr.d = hdr.a[2];
        hdr.e = hdr.a[3];
        hdr.f = hdr.a[4];
        hdr.g = hdr.a.size; //5
        hdr.h = hdr.a.next;
        hdr.i = hdr.a;
        hdr.i.next = {42, 42};
        hdr.j = hdr.i.next;
        hdr.k = set_third(hdr.i);
        hdr.l = hdr.k[3];
        hdr.m = push1(hdr.k);
        hdr.n = hdr.m[0];
        hdr.o = hdr.m[1];
        hdr.p = hdr.m[2];
        hdr.q = hdr.m[3];
        hdr.r = hdr.m[4];
        hdr.s = pop2(hdr.m);
        hdr.t = hdr.s[0];
        hdr.u = hdr.s[1];
        hdr.v = hdr.s[2];
        hdr.w = hdr.s[3];
        hdr.x = hdr.s[4];
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
      packet.emit(hdr.b);
      packet.emit(hdr.c);
      packet.emit(hdr.d);
      packet.emit(hdr.e);
      packet.emit(hdr.f);
      packet.emit(hdr.g);
      packet.emit(hdr.h);
      packet.emit(hdr.j);
      packet.emit(hdr.l);
      packet.emit(hdr.n);
      packet.emit(hdr.o);
      packet.emit(hdr.p);
      packet.emit(hdr.q);
      packet.emit(hdr.r);
      packet.emit(hdr.t);
      packet.emit(hdr.u);
      packet.emit(hdr.v);
      packet.emit(hdr.w);
      packet.emit(hdr.x);
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
