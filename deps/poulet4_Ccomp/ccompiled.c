#include "petr4-runtime.h"
struct _p_e_t_r_4_0b1011;
struct _p_e_t_r_4_0b111;
struct _p_e_t_r_4_0b11;
struct _p_e_t_r_4_0b1011 {
  _Bool _p_e_t_r_4_0b1100;
};

struct _p_e_t_r_4_0b111 {
  struct BitVec *_p_e_t_r_4_0b1000;
};

struct _p_e_t_r_4_0b11 {
  _Bool _p_e_t_r_4_0b100;
};

int main();
void MyDeparser();
void test_deparser();
void MyComputeChecksum();
void test_computeChecksum();
void MyEgress();
void test_egress();
void MyIngress();
void test_ingress();
void MyVerifyChecksum();
void test_verifyChecksum();
void MyParser();
void start();
signed char _p_e_t_r_4_0b100111[2] = { 49, 0, };

int main(void)
{
  struct packet_out _p_e_t_r_4_0b101110;
  struct packet_in _p_e_t_r_4_0b101101;
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b101100;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b101011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b101010;
  MyParser
    (_p_e_t_r_4_0b101101, &_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101011,
     &_p_e_t_r_4_0b101100);
  MyVerifyChecksum(&_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101011);
  MyIngress
    (&_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101011, &_p_e_t_r_4_0b101100);
  MyEgress(&_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101011, &_p_e_t_r_4_0b101100);
  MyComputeChecksum(&_p_e_t_r_4_0b101010, &_p_e_t_r_4_0b101011);
  MyDeparser(_p_e_t_r_4_0b101110, _p_e_t_r_4_0b101010);
}

void MyDeparser(struct packet_out _p_e_t_r_4_0b100010, struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b100011)
{
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b100100;
  _p_e_t_r_4_0b100100 = _p_e_t_r_4_0b100011;
  _p_e_t_r_4_0b100011 = _p_e_t_r_4_0b100100;
}

void test_deparser(struct packet_out _p_e_t_r_4_0b100010, struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b100011)
{
  struct BitVec _p_e_t_r_4_0b101001;
  struct BitVec _p_e_t_r_4_0b101000;
  struct BitVec _p_e_t_r_4_0b100110;
  struct BitVec _p_e_t_r_4_0b100101;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b100100;
  _p_e_t_r_4_0b100100 = _p_e_t_r_4_0b100011;
  init_bitvec(&_p_e_t_r_4_0b100110, 1, 32, _p_e_t_r_4_0b100111);
  init_bitvec(&_p_e_t_r_4_0b101000, 1, 32, _p_e_t_r_4_0b100111);
  interp_bplus
    (&_p_e_t_r_4_0b101001, _p_e_t_r_4_0b100110, _p_e_t_r_4_0b101000);
  _p_e_t_r_4_0b100101 = _p_e_t_r_4_0b101001;
  _p_e_t_r_4_0b100011 = _p_e_t_r_4_0b100100;
}

void MyComputeChecksum(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b11110, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b100000)
{
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b100001;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b11111 = *_p_e_t_r_4_0b11110;
  _p_e_t_r_4_0b100001 = *_p_e_t_r_4_0b100000;
  *_p_e_t_r_4_0b11110 = _p_e_t_r_4_0b11111;
  *_p_e_t_r_4_0b100000 = _p_e_t_r_4_0b100001;
}

void test_computeChecksum(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b11110, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b100000)
{
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b100001;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b11111 = *_p_e_t_r_4_0b11110;
  _p_e_t_r_4_0b100001 = *_p_e_t_r_4_0b100000;
  *_p_e_t_r_4_0b11110 = _p_e_t_r_4_0b11111;
  *_p_e_t_r_4_0b100000 = _p_e_t_r_4_0b100001;
}

void MyEgress(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b11000, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b11010, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b11100)
{
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b11101;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b11011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b11001;
  _p_e_t_r_4_0b11001 = *_p_e_t_r_4_0b11000;
  _p_e_t_r_4_0b11011 = *_p_e_t_r_4_0b11010;
  _p_e_t_r_4_0b11101 = *_p_e_t_r_4_0b11100;
  *_p_e_t_r_4_0b11000 = _p_e_t_r_4_0b11001;
  *_p_e_t_r_4_0b11010 = _p_e_t_r_4_0b11011;
  *_p_e_t_r_4_0b11100 = _p_e_t_r_4_0b11101;
}

void test_egress(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b11000, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b11010, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b11100)
{
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b11101;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b11011;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b11001;
  _p_e_t_r_4_0b11001 = *_p_e_t_r_4_0b11000;
  _p_e_t_r_4_0b11011 = *_p_e_t_r_4_0b11010;
  _p_e_t_r_4_0b11101 = *_p_e_t_r_4_0b11100;
  *_p_e_t_r_4_0b11000 = _p_e_t_r_4_0b11001;
  *_p_e_t_r_4_0b11010 = _p_e_t_r_4_0b11011;
  *_p_e_t_r_4_0b11100 = _p_e_t_r_4_0b11101;
}

void MyIngress(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b10010, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b10100, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b10110)
{
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b10111;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b10101;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b10011;
  _p_e_t_r_4_0b10011 = *_p_e_t_r_4_0b10010;
  _p_e_t_r_4_0b10101 = *_p_e_t_r_4_0b10100;
  _p_e_t_r_4_0b10111 = *_p_e_t_r_4_0b10110;
  *_p_e_t_r_4_0b10010 = _p_e_t_r_4_0b10011;
  *_p_e_t_r_4_0b10100 = _p_e_t_r_4_0b10101;
  *_p_e_t_r_4_0b10110 = _p_e_t_r_4_0b10111;
}

void test_ingress(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b10010, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b10100, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b10110)
{
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b10111;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b10101;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b10011;
  _p_e_t_r_4_0b10011 = *_p_e_t_r_4_0b10010;
  _p_e_t_r_4_0b10101 = *_p_e_t_r_4_0b10100;
  _p_e_t_r_4_0b10111 = *_p_e_t_r_4_0b10110;
  *_p_e_t_r_4_0b10010 = _p_e_t_r_4_0b10011;
  *_p_e_t_r_4_0b10100 = _p_e_t_r_4_0b10101;
  *_p_e_t_r_4_0b10110 = _p_e_t_r_4_0b10111;
}

void MyVerifyChecksum(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b1110, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b10000)
{
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b10001;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b1111;
  _p_e_t_r_4_0b1111 = *_p_e_t_r_4_0b1110;
  _p_e_t_r_4_0b10001 = *_p_e_t_r_4_0b10000;
  *_p_e_t_r_4_0b1110 = _p_e_t_r_4_0b1111;
  *_p_e_t_r_4_0b10000 = _p_e_t_r_4_0b10001;
}

void test_verifyChecksum(struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b1110, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b10000)
{
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b10001;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b1111;
  _p_e_t_r_4_0b1111 = *_p_e_t_r_4_0b1110;
  _p_e_t_r_4_0b10001 = *_p_e_t_r_4_0b10000;
  *_p_e_t_r_4_0b1110 = _p_e_t_r_4_0b1111;
  *_p_e_t_r_4_0b10000 = _p_e_t_r_4_0b10001;
}

void MyParser(struct packet_in _p_e_t_r_4_0b1, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b10, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b110, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b1010)
{
  struct _p_e_t_r_4_0b1011 _p_e_t_r_4_0b1101;
  struct _p_e_t_r_4_0b111 _p_e_t_r_4_0b1001;
  struct _p_e_t_r_4_0b11 _p_e_t_r_4_0b101;
  _p_e_t_r_4_0b101 = *_p_e_t_r_4_0b10;
  _p_e_t_r_4_0b1001 = *_p_e_t_r_4_0b110;
  _p_e_t_r_4_0b1101 = *_p_e_t_r_4_0b1010;
  start
    (_p_e_t_r_4_0b1, &_p_e_t_r_4_0b101, &_p_e_t_r_4_0b1001,
     &_p_e_t_r_4_0b1101);
  *_p_e_t_r_4_0b10 = _p_e_t_r_4_0b101;
  *_p_e_t_r_4_0b110 = _p_e_t_r_4_0b1001;
  *_p_e_t_r_4_0b1010 = _p_e_t_r_4_0b1101;
}

void start(struct packet_in _p_e_t_r_4_0b1, struct _p_e_t_r_4_0b11 *_p_e_t_r_4_0b10, struct _p_e_t_r_4_0b111 *_p_e_t_r_4_0b110, struct _p_e_t_r_4_0b1011 *_p_e_t_r_4_0b1010)
{
  /*skip*/;
  return;
}


