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

    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

  action a() { standard_metadata.egress_spec = 0; }
  action a_with_control_params(bit<9> x) { standard_metadata.egress_spec = x; }

  table my_table {
    key = {standard_metadata.egress_spec : exact;
           standard_metadata.ingress_port : ternary;
          }
    actions = {a;
               a_with_control_params;
               }
    default_action = a();
    const entries = {
                     (9w0, 9w1 &&& 9w1) : a_with_control_params(1);
                     (0x02, 0x1181) : a_with_control_params(2);
                     (0x03, 0x1111) : a_with_control_params(3);
                     (0x04, 0x1211) : a_with_control_params(4);
                     (0x04, 0x1311) : a_with_control_params(5);
                     (0x06, _ ) : a_with_control_params(6);
                    }
      }


    apply {
        my_table.apply();
        exit;
    }

}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr);
    }
}

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
