#include <core.p4>
#include <v1model.p4>

error { MyError };

struct my_struct {
    bit first;
    bool second;
}

struct my_other_struct {
    my_struct first;
    my_struct second;
}

my_other_struct f(inout my_other_struct s) {
    s.first = {1, true};
    s.second = {0, false};
    s.first.first = 0;
    s.first.second = false;
    s.second.first = 1;
    s.second.second = true;
    return s;
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
    apply {
        standard_metadata.egress_port = 9;
    }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { 
      my_struct s1 = (my_struct){1w0, false};
      my_struct s2 = (my_struct){1w1, true};
        /*
      bit test1 = s1.first; //false
      bool test2 = s1.second; //
      bit test3 = s2.first;
      bool test4 = s2.second;
      my_other_struct s3 = {s1, s2};
      my_other_struct s4 = f(s3);
      my_other_struct s5 = {{0,false}, {1,true}};
  
      bool a = error.NoError != error.MyError;
        */
      //bool b = s3.first != s3.second;
      //bool c = s3 == s4;
      //bool d = s4 == s5;
      // packet.emit(s1);
      // packet.emit(s2);
      //packet.emit((bit<8>) test1);
      //packet.emit((bit<8>) ((bit) test2));
      //packet.emit((bit<8>) test3);
      //packet.emit((bit<8>) ((bit) test4));
      // packet.emit(s3);
      // packet.emit(s4);
      // packet.emit(s5);
      //packet.emit((bit<8>) ((bit) a));
      //packet.emit((bit<8>) ((bit) b));
      //packet.emit((bit<8>) ((bit) c));
      //packet.emit((bit<8>) ((bit) d));
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
