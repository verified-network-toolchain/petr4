#include <core.p4>
#include <v1model.p4>

header head {
    bit<8> v;
}

struct metadata { }

parser MyParser(packet_in packet,
                out head[13] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }

}

control MyChecksum(inout head[13] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout head[13] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        standard_metadata.egress_spec = 1;

    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

  action a() { 
      hdr[0].v = 0;
      hdr[0].setValid();
  }

  action a_with_control_params(bit<8> x) { 
      hdr[0].v = x;
      hdr[0].setValid();
  }

  table my_table {
    key = {standard_metadata.egress_spec : exact;
           standard_metadata.ingress_port : ternary;
          }
    actions = {a;
               a_with_control_params;
               }
    default_action = a();
    const entries = {
                     (9w0, 9w1 &&& 9w0) : a_with_control_params(1);
                     (0x02, 0x1181) : a_with_control_params(2);
                     (0x03, 0x1111) : a_with_control_params(3);
                     (0x04, 0x1211) : a_with_control_params(4);
                     (0x04, 0x1311) : a_with_control_params(5);
                     (0x06, _ ) : a_with_control_params(6);
                    }
      }


    apply {
        standard_metadata.egress_spec = 6;
        standard_metadata.ingress_port = 1;
        my_table.apply();
        exit;
    }

}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr[0]);
    }
}

//TODO: blocking on stf update

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
