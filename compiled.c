#include "Petr4Runtime.h"
struct M;
struct standard_metadata_t;
struct M {
};

struct standard_metadata_t {
  struct BitVec *ingress_port;
  struct BitVec *egress_spec;
  struct BitVec *egress_port;
  struct BitVec *instance_type;
  struct BitVec *packet_length;
  struct BitVec *enq_timestamp;
  struct BitVec *enq_qdepth;
  struct BitVec *deq_timedelta;
  struct BitVec *deq_qdepth;
  struct BitVec *ingress_global_timestamp;
  struct BitVec *egress_global_timestamp;
  struct BitVec *mcast_grp;
  struct BitVec *egress_rid;
  struct BitVec *checksum_error;
  unsigned int parser_error;
  struct BitVec *priority;
};

void main();
_Bool parser();
_Bool start();
_Bool deparser();
_Bool compute();
_Bool egress();
_Bool ingress();
_Bool verify();
_Bool $DUMMY_ACTION();
void main(void)
{
  /*skip*/;
}

_Bool parser(void *_p_e_t_r_4_0b100101, struct M *_p_e_t_r_4_0b100111, struct M *_p_e_t_r_4_0b101001, struct standard_metadata_t *_p_e_t_r_4_0b101011)
{
  struct standard_metadata_t _p_e_t_r_4_0b101100;
  struct M _p_e_t_r_4_0b101010;
  struct M _p_e_t_r_4_0b101000;
  void _p_e_t_r_4_0b100110;
  _p_e_t_r_4_0b100110 = *_p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b101000 = *_p_e_t_r_4_0b100111;
  _p_e_t_r_4_0b101010 = *_p_e_t_r_4_0b101001;
  _p_e_t_r_4_0b101100 = *_p_e_t_r_4_0b101011;
  start
    (&_p_e_t_r_4_0b100110, &_p_e_t_r_4_0b101000, &_p_e_t_r_4_0b101010,
     &_p_e_t_r_4_0b101100);
  *_p_e_t_r_4_0b100101 = _p_e_t_r_4_0b100110;
  *_p_e_t_r_4_0b100111 = _p_e_t_r_4_0b101000;
  *_p_e_t_r_4_0b101001 = _p_e_t_r_4_0b101010;
  *_p_e_t_r_4_0b101011 = _p_e_t_r_4_0b101100;
}

_Bool start(void *_p_e_t_r_4_0b100101, struct M *_p_e_t_r_4_0b100111, struct M *_p_e_t_r_4_0b101001, struct standard_metadata_t *_p_e_t_r_4_0b101011)
{
  return 1;
}

_Bool deparser(void *_p_e_t_r_4_0b11111, struct M _p_e_t_r_4_0b100001)
{
  struct M _p_e_t_r_4_0b100010;
  void _p_e_t_r_4_0b100000;
  _p_e_t_r_4_0b100000 = *_p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b100010 = _p_e_t_r_4_0b100001;
  *_p_e_t_r_4_0b11111 = _p_e_t_r_4_0b100000;
  _p_e_t_r_4_0b100001 = _p_e_t_r_4_0b100010;
}

_Bool compute(struct M *_p_e_t_r_4_0b11010, struct M *_p_e_t_r_4_0b11100)
{
  struct M _p_e_t_r_4_0b11101;
  struct M _p_e_t_r_4_0b11011;
  _p_e_t_r_4_0b11011 = *_p_e_t_r_4_0b11010;
  _p_e_t_r_4_0b11101 = *_p_e_t_r_4_0b11100;
  *_p_e_t_r_4_0b11010 = _p_e_t_r_4_0b11011;
  *_p_e_t_r_4_0b11100 = _p_e_t_r_4_0b11101;
}

_Bool egress(struct M *_p_e_t_r_4_0b10011, struct M *_p_e_t_r_4_0b10101, struct standard_metadata_t *_p_e_t_r_4_0b10111)
{
  struct standard_metadata_t _p_e_t_r_4_0b11000;
  struct M _p_e_t_r_4_0b10110;
  struct M _p_e_t_r_4_0b10100;
  _p_e_t_r_4_0b10100 = *_p_e_t_r_4_0b10011;
  _p_e_t_r_4_0b10110 = *_p_e_t_r_4_0b10101;
  _p_e_t_r_4_0b11000 = *_p_e_t_r_4_0b10111;
  *_p_e_t_r_4_0b10011 = _p_e_t_r_4_0b10100;
  *_p_e_t_r_4_0b10101 = _p_e_t_r_4_0b10110;
  *_p_e_t_r_4_0b10111 = _p_e_t_r_4_0b11000;
}

_Bool ingress(struct M *_p_e_t_r_4_0b1100, struct M *_p_e_t_r_4_0b1110, struct standard_metadata_t *_p_e_t_r_4_0b10000)
{
  struct standard_metadata_t _p_e_t_r_4_0b10001;
  struct M _p_e_t_r_4_0b1111;
  struct M _p_e_t_r_4_0b1101;
  _p_e_t_r_4_0b1101 = *_p_e_t_r_4_0b1100;
  _p_e_t_r_4_0b1111 = *_p_e_t_r_4_0b1110;
  _p_e_t_r_4_0b10001 = *_p_e_t_r_4_0b10000;
  *_p_e_t_r_4_0b1100 = _p_e_t_r_4_0b1101;
  *_p_e_t_r_4_0b1110 = _p_e_t_r_4_0b1111;
  *_p_e_t_r_4_0b10000 = _p_e_t_r_4_0b10001;
}

_Bool verify(struct M *_p_e_t_r_4_0b111, struct M *_p_e_t_r_4_0b1001)
{
  struct M _p_e_t_r_4_0b1010;
  struct M _p_e_t_r_4_0b1000;
  _p_e_t_r_4_0b1000 = *_p_e_t_r_4_0b111;
  _p_e_t_r_4_0b1010 = *_p_e_t_r_4_0b1001;
  *_p_e_t_r_4_0b111 = _p_e_t_r_4_0b1000;
  *_p_e_t_r_4_0b1001 = _p_e_t_r_4_0b1010;
}

_Bool $DUMMY_ACTION(void *_p_e_t_r_4_0b11111, struct M _p_e_t_r_4_0b100001)
{
  struct M _p_e_t_r_4_0b100010;
  void _p_e_t_r_4_0b100000;
  _p_e_t_r_4_0b100000 = *_p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b100010 = _p_e_t_r_4_0b100001;
  *_p_e_t_r_4_0b11111 = _p_e_t_r_4_0b100000;
  _p_e_t_r_4_0b100001 = _p_e_t_r_4_0b100010;
}


