#include "Petr4Runtime.h"
struct _p_e_t_r_4_0b11;
struct _p_e_t_r_4_0b1;
struct _p_e_t_r_4_0b11 {
};

struct _p_e_t_r_4_0b1 {
  _Bool _p_e_t_r_4_0b10;
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
signed char _p_e_t_r_4_0b11010[3] = { 55, 53, 0, };

signed char _p_e_t_r_4_0b11000[4] = { 49, 49, 55, 0, };

signed char _p_e_t_r_4_0b10110[3] = { 52, 50, 0, };

void dummy_main(void)
{
  /*skip*/;
}

_Bool parser(struct packet_in *_p_e_t_r_4_0b101111, struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b110000, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b110010, struct standard_metadata_t *_p_e_t_r_4_0b110100)
{
  struct standard_metadata_t _p_e_t_r_4_0b110101;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b110011;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b110001;
  _p_e_t_r_4_0b110001 = *_p_e_t_r_4_0b110000;
  _p_e_t_r_4_0b110011 = *_p_e_t_r_4_0b110010;
  _p_e_t_r_4_0b110101 = *_p_e_t_r_4_0b110100;
  start
    (_p_e_t_r_4_0b101111, &_p_e_t_r_4_0b110001, &_p_e_t_r_4_0b110011,
     &_p_e_t_r_4_0b110101);
  *_p_e_t_r_4_0b110000 = _p_e_t_r_4_0b110001;
  *_p_e_t_r_4_0b110010 = _p_e_t_r_4_0b110011;
  *_p_e_t_r_4_0b110100 = _p_e_t_r_4_0b110101;
  return 1;
}

_Bool start(struct packet_in *_p_e_t_r_4_0b111101, struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b111110, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b1000000, struct standard_metadata_t *_p_e_t_r_4_0b1000010)
{
  struct standard_metadata_t _p_e_t_r_4_0b1000011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b1000001;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b111111;
  _p_e_t_r_4_0b111111 = *_p_e_t_r_4_0b111110;
  _p_e_t_r_4_0b1000001 = *_p_e_t_r_4_0b1000000;
  _p_e_t_r_4_0b1000011 = *_p_e_t_r_4_0b1000010;
  /*skip*/;
  extract_bool(_p_e_t_r_4_0b111101, &_p_e_t_r_4_0b111111._p_e_t_r_4_0b10);
  *_p_e_t_r_4_0b111110 = _p_e_t_r_4_0b111111;
  *_p_e_t_r_4_0b1000000 = _p_e_t_r_4_0b1000001;
  *_p_e_t_r_4_0b1000010 = _p_e_t_r_4_0b1000011;
  return 1;
  *_p_e_t_r_4_0b111110 = _p_e_t_r_4_0b111111;
  *_p_e_t_r_4_0b1000000 = _p_e_t_r_4_0b1000001;
  *_p_e_t_r_4_0b1000010 = _p_e_t_r_4_0b1000011;
}

_Bool deparser(struct packet_out *_p_e_t_r_4_0b101010, struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101011)
{
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101100;
  /*skip*/;
  _p_e_t_r_4_0b101100 = _p_e_t_r_4_0b101011;
  /*skip*/;
  /*skip*/;
  emit_bool(_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101100._p_e_t_r_4_0b10);
  _p_e_t_r_4_0b101011 = _p_e_t_r_4_0b101100;
  return 1;
}

_Bool compute(struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b100101, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b100111)
{
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b101000;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b100110;
  /*skip*/;
  _p_e_t_r_4_0b100110 = *_p_e_t_r_4_0b100101;
  _p_e_t_r_4_0b101000 = *_p_e_t_r_4_0b100111;
  /*skip*/;
  *_p_e_t_r_4_0b100101 = _p_e_t_r_4_0b100110;
  *_p_e_t_r_4_0b100111 = _p_e_t_r_4_0b101000;
  return 1;
}

_Bool egress(struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b11110, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b100000, struct standard_metadata_t *_p_e_t_r_4_0b100010)
{
  struct standard_metadata_t _p_e_t_r_4_0b100011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b100001;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b11111;
  /*skip*/;
  _p_e_t_r_4_0b11111 = *_p_e_t_r_4_0b11110;
  _p_e_t_r_4_0b100001 = *_p_e_t_r_4_0b100000;
  _p_e_t_r_4_0b100011 = *_p_e_t_r_4_0b100010;
  /*skip*/;
  *_p_e_t_r_4_0b11110 = _p_e_t_r_4_0b11111;
  *_p_e_t_r_4_0b100000 = _p_e_t_r_4_0b100001;
  *_p_e_t_r_4_0b100010 = _p_e_t_r_4_0b100011;
  return 1;
}

_Bool ingress(struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b1110, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b10000, struct standard_metadata_t *_p_e_t_r_4_0b10010)
{
  _Bool _p_e_t_r_4_0b11100;
  struct BitVec _p_e_t_r_4_0b11011;
  struct BitVec _p_e_t_r_4_0b11001;
  struct BitVec _p_e_t_r_4_0b10111;
  struct BitVec _p_e_t_r_4_0b10101;
  _Bool _p_e_t_r_4_0b10100;
  struct standard_metadata_t _p_e_t_r_4_0b10011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b10001;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b1111;
  /*skip*/;
  _p_e_t_r_4_0b1111 = *_p_e_t_r_4_0b1110;
  _p_e_t_r_4_0b10001 = *_p_e_t_r_4_0b10000;
  _p_e_t_r_4_0b10011 = *_p_e_t_r_4_0b10010;
  /*skip*/;
  init_bitvec(&_p_e_t_r_4_0b10101, 1, 8, _p_e_t_r_4_0b10110);
  init_bitvec(&_p_e_t_r_4_0b10111, 1, 8, _p_e_t_r_4_0b11000);
  init_bitvec(&_p_e_t_r_4_0b11001, 1, 8, _p_e_t_r_4_0b11010);
  interp_bminus_sat
    (&_p_e_t_r_4_0b11011, _p_e_t_r_4_0b10111, _p_e_t_r_4_0b11001);
  interp_beq(&_p_e_t_r_4_0b11100, _p_e_t_r_4_0b10101, _p_e_t_r_4_0b11011);
  _p_e_t_r_4_0b10100 = _p_e_t_r_4_0b11100;
  _p_e_t_r_4_0b1111._p_e_t_r_4_0b10 = _p_e_t_r_4_0b10100;
  *_p_e_t_r_4_0b1110 = _p_e_t_r_4_0b1111;
  *_p_e_t_r_4_0b10000 = _p_e_t_r_4_0b10001;
  *_p_e_t_r_4_0b10010 = _p_e_t_r_4_0b10011;
  return 1;
}

_Bool verify(struct _p_e_t_r_4_0b1 *_p_e_t_r_4_0b1001, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b1011)
{
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b1100;
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b1010;
  /*skip*/;
  _p_e_t_r_4_0b1010 = *_p_e_t_r_4_0b1001;
  _p_e_t_r_4_0b1100 = *_p_e_t_r_4_0b1011;
  /*skip*/;
  *_p_e_t_r_4_0b1001 = _p_e_t_r_4_0b1010;
  *_p_e_t_r_4_0b1011 = _p_e_t_r_4_0b1100;
  return 1;
}

_Bool $DUMMY_ACTION(struct packet_out *_p_e_t_r_4_0b101010, struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101011)
{
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101100;
  _p_e_t_r_4_0b101100 = _p_e_t_r_4_0b101011;
  _p_e_t_r_4_0b101011 = _p_e_t_r_4_0b101100;
}

_Bool NoAction(struct packet_out *_p_e_t_r_4_0b101010, struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101011)
{
  struct _p_e_t_r_4_0b1 _p_e_t_r_4_0b101100;
  _p_e_t_r_4_0b101100 = _p_e_t_r_4_0b101011;
  _p_e_t_r_4_0b101011 = _p_e_t_r_4_0b101100;
}


typedef struct _p_e_t_r_4_0b1 H; 
typedef struct _p_e_t_r_4_0b11 M; 
