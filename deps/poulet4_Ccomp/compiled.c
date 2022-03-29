#include "Petr4Runtime.h"
struct M;
struct H;
struct standard_metadata_t;
struct M {
};

struct H {
  _Bool _p_e_t_r_4_0b10;
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

void dummy_main();
_Bool parser();
_Bool start();
_Bool deparser();
_Bool compute();
_Bool egress();
_Bool ingress();
_Bool verify();
_Bool $DUMMY_ACTION();
_Bool NoAction();
signed char _p_e_t_r_4_0b10101[2] = { 57, 0, };

void dummy_main(void)
{
  /*skip*/;
}

_Bool parser(struct packet_in *_p_e_t_r_4_0b101010, struct H *_p_e_t_r_4_0b101100, struct M *_p_e_t_r_4_0b101110, struct standard_metadata_t *_p_e_t_r_4_0b110000)
{
  struct standard_metadata_t _p_e_t_r_4_0b110001;
  struct M _p_e_t_r_4_0b101111;
  struct H _p_e_t_r_4_0b101101;
  struct packet_in _p_e_t_r_4_0b101011;
  _p_e_t_r_4_0b101011 = *_p_e_t_r_4_0b101010;
  _p_e_t_r_4_0b101101 = *_p_e_t_r_4_0b101100;
  _p_e_t_r_4_0b101111 = *_p_e_t_r_4_0b101110;
  _p_e_t_r_4_0b110001 = *_p_e_t_r_4_0b110000;
  start
    (&_p_e_t_r_4_0b101011, &_p_e_t_r_4_0b101101, &_p_e_t_r_4_0b101111,
     &_p_e_t_r_4_0b110001);
  *_p_e_t_r_4_0b101010 = _p_e_t_r_4_0b101011;
  *_p_e_t_r_4_0b101100 = _p_e_t_r_4_0b101101;
  *_p_e_t_r_4_0b101110 = _p_e_t_r_4_0b101111;
  *_p_e_t_r_4_0b110000 = _p_e_t_r_4_0b110001;
  return 1;
}

_Bool start(struct packet_in *_p_e_t_r_4_0b101010, struct H *_p_e_t_r_4_0b101100, struct M *_p_e_t_r_4_0b101110, struct standard_metadata_t *_p_e_t_r_4_0b110000)
{
  /*skip*/;
  return 1;
}

_Bool deparser(struct packet_out *_p_e_t_r_4_0b100100, struct H _p_e_t_r_4_0b100110)
{
  struct H _p_e_t_r_4_0b100111;
  struct packet_out _p_e_t_r_4_0b100101;
  /*skip*/;
  _p_e_t_r_4_0b100101 = *_p_e_t_r_4_0b100100;
  _p_e_t_r_4_0b100111 = _p_e_t_r_4_0b100110;
  /*skip*/;
  *_p_e_t_r_4_0b100100 = _p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b100110 = _p_e_t_r_4_0b100111;
  return 1;
}

_Bool compute(struct H *_p_e_t_r_4_0b11111, struct M *_p_e_t_r_4_0b100001)
{
  struct M _p_e_t_r_4_0b100010;
  struct H _p_e_t_r_4_0b100000;
  /*skip*/;
  _p_e_t_r_4_0b100000 = *_p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b100010 = *_p_e_t_r_4_0b100001;
  /*skip*/;
  *_p_e_t_r_4_0b11111 = _p_e_t_r_4_0b100000;
  *_p_e_t_r_4_0b100001 = _p_e_t_r_4_0b100010;
  return 1;
}

_Bool egress(struct H *_p_e_t_r_4_0b10111, struct M *_p_e_t_r_4_0b11001, struct standard_metadata_t *_p_e_t_r_4_0b11011)
{
  struct BitVec _p_e_t_r_4_0b11101;
  struct standard_metadata_t _p_e_t_r_4_0b11100;
  struct M _p_e_t_r_4_0b11010;
  struct H _p_e_t_r_4_0b11000;
  /*skip*/;
  _p_e_t_r_4_0b11000 = *_p_e_t_r_4_0b10111;
  _p_e_t_r_4_0b11010 = *_p_e_t_r_4_0b11001;
  _p_e_t_r_4_0b11100 = *_p_e_t_r_4_0b11011;
  /*skip*/;
  init_bitvec(&_p_e_t_r_4_0b11101, 0, 9, _p_e_t_r_4_0b10101);
  *_p_e_t_r_4_0b11100.egress_port = _p_e_t_r_4_0b11101;
  *_p_e_t_r_4_0b10111 = _p_e_t_r_4_0b11000;
  *_p_e_t_r_4_0b11001 = _p_e_t_r_4_0b11010;
  *_p_e_t_r_4_0b11011 = _p_e_t_r_4_0b11100;
  return 1;
}

_Bool ingress(struct H *_p_e_t_r_4_0b1110, struct M *_p_e_t_r_4_0b10000, struct standard_metadata_t *_p_e_t_r_4_0b10010)
{
  struct BitVec _p_e_t_r_4_0b10100;
  struct standard_metadata_t _p_e_t_r_4_0b10011;
  struct M _p_e_t_r_4_0b10001;
  struct H _p_e_t_r_4_0b1111;
  /*skip*/;
  _p_e_t_r_4_0b1111 = *_p_e_t_r_4_0b1110;
  _p_e_t_r_4_0b10001 = *_p_e_t_r_4_0b10000;
  _p_e_t_r_4_0b10011 = *_p_e_t_r_4_0b10010;
  /*skip*/;
  _p_e_t_r_4_0b1111._p_e_t_r_4_0b10 = 1;
  init_bitvec(&_p_e_t_r_4_0b10100, 0, 9, _p_e_t_r_4_0b10101);
  *_p_e_t_r_4_0b10011.egress_spec = _p_e_t_r_4_0b10100;
  *_p_e_t_r_4_0b1110 = _p_e_t_r_4_0b1111;
  *_p_e_t_r_4_0b10000 = _p_e_t_r_4_0b10001;
  *_p_e_t_r_4_0b10010 = _p_e_t_r_4_0b10011;
  return 1;
}

_Bool verify(struct H *_p_e_t_r_4_0b1001, struct M *_p_e_t_r_4_0b1011)
{
  struct M _p_e_t_r_4_0b1100;
  struct H _p_e_t_r_4_0b1010;
  /*skip*/;
  _p_e_t_r_4_0b1010 = *_p_e_t_r_4_0b1001;
  _p_e_t_r_4_0b1100 = *_p_e_t_r_4_0b1011;
  /*skip*/;
  *_p_e_t_r_4_0b1001 = _p_e_t_r_4_0b1010;
  *_p_e_t_r_4_0b1011 = _p_e_t_r_4_0b1100;
  return 1;
}

_Bool $DUMMY_ACTION(struct packet_out *_p_e_t_r_4_0b100100, struct H _p_e_t_r_4_0b100110)
{
  struct H _p_e_t_r_4_0b100111;
  struct packet_out _p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b100101 = *_p_e_t_r_4_0b100100;
  _p_e_t_r_4_0b100111 = _p_e_t_r_4_0b100110;
  *_p_e_t_r_4_0b100100 = _p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b100110 = _p_e_t_r_4_0b100111;
}

_Bool NoAction(struct packet_out *_p_e_t_r_4_0b100100, struct H _p_e_t_r_4_0b100110)
{
  struct H _p_e_t_r_4_0b100111;
  struct packet_out _p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b100101 = *_p_e_t_r_4_0b100100;
  _p_e_t_r_4_0b100111 = _p_e_t_r_4_0b100110;
  *_p_e_t_r_4_0b100100 = _p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b100110 = _p_e_t_r_4_0b100111;
}


