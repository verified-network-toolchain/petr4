/*
 * Author: Hardik Soni
 * Email: hks57@cornell.edu
 */

#ifndef _MSA_P4_
#define _MSA_P4_

#include <core.p4>

typedef   bit<9>    PortId_t;
typedef   bit<16>   PktInstId_t;
typedef   bit<16>   GroupId_t;
const   PortId_t    PORT_CPU = 255;
const   PortId_t    PORT_RECIRCULATE = 254;

enum metadata_fields_t {
  QUEUE_DEPTH_AT_DEQUEUE
}

extern im_t {
  void set_out_port(in PortId_t out_port);
  PortId_t get_in_port();
  PortId_t get_out_port(); // default 0x00
  bit<32> get_value(metadata_fields_t field_type);
  // void copy_from(im_t im); TODO fix checker bug thing
  void drop();
}

action msa_no_action(){}

parser micro_parser<H, M, I, IO>(
    packet_in packet,
    im_t im,
    out H hdrs,
    inout M meta,
    in I in_param,
    inout IO inout_param);

control micro_control<H, M, I, O, IO>(
    im_t im,
    inout H hdrs,
    inout M meta,
    in I in_param,
    out O out_param,
    inout IO inout_param);
    
control micro_deparser<H>(packet_out packet, in H hdrs);

package uP4Switch<H, M, I, O, IO>(
    micro_parser<H, M, I, IO> p,
    micro_control<H, M, I, O, IO> c,
    micro_deparser<H> d);

#endif  /* _msa_P4_ */