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
                out headers hdr_out,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        headers hdr;
        /*
        hdr.a = init(); //5 invalid headers
        hdr.b = hdr.a[0]; //one invalid header
        hdr.c = hdr.a[1]; //one invalid header
        hdr.d = hdr.a[2]; //one invlaid header
        hdr.e = hdr.a[3]; //one invalid header
        hdr.f = hdr.a[4]; //one invalid header
        hdr.g = hdr.a.size; //5
        hdr.h = hdr.a.next; //one invalid header
        hdr.i = hdr.a; //copy a into i
        hdr.i.next = {42, 42}; //set the first header in i to valid and inc next
        hdr.j = hdr.i.next; //next should be 1; j is invalid
        hdr.k = set_third(hdr.i); //next of k is 1, copies i and sets the third header
        hdr.l = hdr.k[3]; // copies the newly init header into l
        hdr.m = push1(hdr.k); //slide it back once, next is now 2
        hdr.n = hdr.m[0]; // invalid
        hdr.o = hdr.m[1]; // valid
        hdr.p = hdr.m[2]; // invalid
        hdr.q = hdr.m[3]; // invalid
        hdr.r = hdr.m[4]; // valid
        hdr.s = pop2(hdr.m); //slide it back once, next is now 0 again
        hdr.t = hdr.s[0]; //invalid
        hdr.u = hdr.s[1]; //invalid
        hdr.v = hdr.s[2]; //valid
        hdr.w = hdr.s[3]; //invalid
        hdr.x = hdr.s[4]; //invalid
        */
        hdr_out = hdr;
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
        /*
      packet.emit(hdr.b); //nop
      packet.emit(hdr.c); //nop
      packet.emit(hdr.d); //nop
      packet.emit(hdr.e); //nop
      packet.emit(hdr.f); //nop
      packet.emit(hdr.g); //emit 0000 0005
      packet.emit(hdr.h); //nop
      packet.emit(hdr.j); //nop
      packet.emit(hdr.l); //emit 2A2A
      packet.emit(hdr.n); //nop
      packet.emit(hdr.o); //emit 2A2A
      packet.emit(hdr.p); //nop
      packet.emit(hdr.q); //nop
      packet.emit(hdr.r); //emit 2A2A
      packet.emit(hdr.t); //nop
      packet.emit(hdr.u); //nop
      packet.emit(hdr.v); //emit 2A2A
      packet.emit(hdr.w); //nop 
      packet.emit(hdr.x); //nop
        */
      //final expected output 0000 0005 2A2A 2A2A 2A2A 2A2A
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
