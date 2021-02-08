error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument, HOBO
}
match_kind {
  exact, ternary, lpm
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
action NoAction() { 
}
typedef bit<9> PortId_t;
typedef bit<16> PktInstId_t;
typedef bit<16> GroupId_t;
const PortId_t PORT_CPU = 255;
const PortId_t PORT_RECIRCULATE = 254;
enum metadata_fields_t {
  QUEUE_DEPTH_AT_DEQUEUE
}
extern im_t {
  void set_out_port(in PortId_t out_port);
  PortId_t get_in_port();
  PortId_t get_out_port();
  bit<32> get_value(metadata_fields_t field_type);
  void drop();
}

action msa_no_action() { 
}
parser micro_parser<H, M, I, IO>
  (packet_in packet,
   im_t im,
   out H hdrs,
   inout M meta,
   in I in_param,
   inout IO inout_param);
control micro_control<H3, M4, I5, O, IO6>
  (im_t im,
   inout H3 hdrs,
   inout M4 meta,
   in I5 in_param,
   out O out_param,
   inout IO6 inout_param);
control micro_deparser<H7> (packet_out packet, in H7 hdrs);
package uP4Switch<H8, M9, I10, O11, IO12>
  (micro_parser<H8, M9, I10, IO12> p,
   micro_control<H8, M9, I10, O11, IO12> c,
   micro_deparser<H8> d);
struct empty_t {
  
}
struct hdr_t {
  
}
parser MyParser1(packet_in packet, im_t im, out hdr_t hdrs,
                 inout empty_t meta, in empty_t in_param,
                 inout empty_t inout_param) {
  state start {
    transition accept;
  }
}
control MyControl1(im_t im, inout hdr_t hdrs, inout empty_t meta,
                   in empty_t in_param, out empty_t out_param,
                   inout empty_t inout_param) {
  apply { 
  }
}
parser MyParser2(packet_in packet, im_t im, out hdr_t hdrs,
                 inout empty_t meta, in empty_t in_param,
                 inout empty_t inout_param) {
  state start {
    transition accept;
  }
}
control MyControl2(im_t im, inout hdr_t hdrs, inout empty_t meta,
                   in empty_t in_param, out empty_t out_param,
                   inout empty_t inout_param) {
  apply { 
  }
}
parser NewParser(packet_in packet, im_t im, out hdr_t hdrs,
                 inout empty_t meta, in empty_t in_param,
                 inout empty_t inout_param) {
  MyParser2() parser2;
  MyParser1() parser1;
  state low_ports_state
    {
    MyParser1.apply(packet, im, hdrs, meta, in_param, inout_param);
    transition accept;
  }
  state high_ports_state
    {
    MyParser2.apply(packet, im, hdrs, meta, in_param, inout_param);
    transition accept;
  }
  state start
    {
    transition select(im.get_in_port()) {
      0 .. 8: low_ports_state;
      8 .. 65353: high_ports_state;
    }
  }
}
control NewControl(im_t im, inout hdr_t hdrs, inout empty_t meta,
                   in empty_t in_param, out empty_t out_param,
                   inout empty_t inout_param) {
  MyControl2() control2;
  MyControl1() control1;
  apply
    {
    if (im.get_in_port()<=8)
      
      control1.apply(im, hdrs, meta, in_param, out_param, inout_param);
      else
        control2.apply(im, hdrs, meta, in_param, out_param, inout_param);
  }
}
control NewDeparser(packet_out packet, in hdr_t hdrs) {
  apply { 
  }
}
uP4Switch(NewParser(), NewControl(), NewDeparser()) main;

