struct _585;
struct BitVec;
struct __petr4_0b10000;
struct __petr4_0b1100;
struct __petr4_0b1000;
struct _585 {
  int _mp_alloc;
  int _mp_size;
  unsigned long long *_mp_d;
};

struct BitVec {
  int is_signed;
  int width;
  struct _585 value[1];
};

struct __petr4_0b10000 {
  _Bool __petr4_0b10001;
};

struct __petr4_0b1100 {
  struct BitVec __petr4_0b1101;
};

struct __petr4_0b1000 {
  _Bool __petr4_0b1001;
};

void __petr4_0b101();
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
void __petr4_0b101(void)
{
  void *__petr4_0b110010;
  void *__petr4_0b110001;
  struct __petr4_0b10000 __petr4_0b110000;
  struct __petr4_0b1100 __petr4_0b101111;
  struct __petr4_0b1000 __petr4_0b101110;
  MyParser
    (__petr4_0b110001, &__petr4_0b101110, &__petr4_0b101111,
     &__petr4_0b110000);
  MyVerifyChecksum(&__petr4_0b101110, &__petr4_0b101111);
  MyIngress(&__petr4_0b101110, &__petr4_0b101111, &__petr4_0b110000);
  MyEgress(&__petr4_0b101110, &__petr4_0b101111, &__petr4_0b110000);
  MyComputeChecksum(&__petr4_0b101110, &__petr4_0b101111);
  MyDeparser(&__petr4_0b110010, __petr4_0b101110);
}

void MyDeparser(void *__petr4_0b100111, struct __petr4_0b1000 __petr4_0b101000)
{
  struct __petr4_0b1000 __petr4_0b101001;
  __petr4_0b101001 = __petr4_0b101000;
  __petr4_0b101000 = __petr4_0b101001;
}

void test_deparser(void *__petr4_0b100111, struct __petr4_0b1000 __petr4_0b101000)
{
  struct BitVec __petr4_0b101101;
  struct BitVec __petr4_0b101100;
  struct BitVec __petr4_0b101011;
  struct BitVec __petr4_0b101010;
  struct __petr4_0b1000 __petr4_0b101001;
  __petr4_0b101001 = __petr4_0b101000;
  /*skip*/;
  /*skip*/;
  eval_plus(&__petr4_0b101011, &__petr4_0b101100, &__petr4_0b101101);
  __petr4_0b101010 = __petr4_0b101101;
  __petr4_0b101000 = __petr4_0b101001;
}

void MyComputeChecksum(struct __petr4_0b1000 *__petr4_0b100011, struct __petr4_0b1100 *__petr4_0b100101)
{
  struct __petr4_0b1100 __petr4_0b100110;
  struct __petr4_0b1000 __petr4_0b100100;
  __petr4_0b100100 = *__petr4_0b100011;
  __petr4_0b100110 = *__petr4_0b100101;
  *__petr4_0b100011 = __petr4_0b100100;
  *__petr4_0b100101 = __petr4_0b100110;
}

void test_computeChecksum(struct __petr4_0b1000 *__petr4_0b100011, struct __petr4_0b1100 *__petr4_0b100101)
{
  struct __petr4_0b1100 __petr4_0b100110;
  struct __petr4_0b1000 __petr4_0b100100;
  __petr4_0b100100 = *__petr4_0b100011;
  __petr4_0b100110 = *__petr4_0b100101;
  *__petr4_0b100011 = __petr4_0b100100;
  *__petr4_0b100101 = __petr4_0b100110;
}

void MyEgress(struct __petr4_0b1000 *__petr4_0b11101, struct __petr4_0b1100 *__petr4_0b11111, struct __petr4_0b10000 *__petr4_0b100001)
{
  struct __petr4_0b10000 __petr4_0b100010;
  struct __petr4_0b1100 __petr4_0b100000;
  struct __petr4_0b1000 __petr4_0b11110;
  __petr4_0b11110 = *__petr4_0b11101;
  __petr4_0b100000 = *__petr4_0b11111;
  __petr4_0b100010 = *__petr4_0b100001;
  *__petr4_0b11101 = __petr4_0b11110;
  *__petr4_0b11111 = __petr4_0b100000;
  *__petr4_0b100001 = __petr4_0b100010;
}

void test_egress(struct __petr4_0b1000 *__petr4_0b11101, struct __petr4_0b1100 *__petr4_0b11111, struct __petr4_0b10000 *__petr4_0b100001)
{
  struct __petr4_0b10000 __petr4_0b100010;
  struct __petr4_0b1100 __petr4_0b100000;
  struct __petr4_0b1000 __petr4_0b11110;
  __petr4_0b11110 = *__petr4_0b11101;
  __petr4_0b100000 = *__petr4_0b11111;
  __petr4_0b100010 = *__petr4_0b100001;
  *__petr4_0b11101 = __petr4_0b11110;
  *__petr4_0b11111 = __petr4_0b100000;
  *__petr4_0b100001 = __petr4_0b100010;
}

void MyIngress(struct __petr4_0b1000 *__petr4_0b10111, struct __petr4_0b1100 *__petr4_0b11001, struct __petr4_0b10000 *__petr4_0b11011)
{
  struct __petr4_0b10000 __petr4_0b11100;
  struct __petr4_0b1100 __petr4_0b11010;
  struct __petr4_0b1000 __petr4_0b11000;
  __petr4_0b11000 = *__petr4_0b10111;
  __petr4_0b11010 = *__petr4_0b11001;
  __petr4_0b11100 = *__petr4_0b11011;
  *__petr4_0b10111 = __petr4_0b11000;
  *__petr4_0b11001 = __petr4_0b11010;
  *__petr4_0b11011 = __petr4_0b11100;
}

void test_ingress(struct __petr4_0b1000 *__petr4_0b10111, struct __petr4_0b1100 *__petr4_0b11001, struct __petr4_0b10000 *__petr4_0b11011)
{
  struct __petr4_0b10000 __petr4_0b11100;
  struct __petr4_0b1100 __petr4_0b11010;
  struct __petr4_0b1000 __petr4_0b11000;
  __petr4_0b11000 = *__petr4_0b10111;
  __petr4_0b11010 = *__petr4_0b11001;
  __petr4_0b11100 = *__petr4_0b11011;
  *__petr4_0b10111 = __petr4_0b11000;
  *__petr4_0b11001 = __petr4_0b11010;
  *__petr4_0b11011 = __petr4_0b11100;
}

void MyVerifyChecksum(struct __petr4_0b1000 *__petr4_0b10011, struct __petr4_0b1100 *__petr4_0b10101)
{
  struct __petr4_0b1100 __petr4_0b10110;
  struct __petr4_0b1000 __petr4_0b10100;
  __petr4_0b10100 = *__petr4_0b10011;
  __petr4_0b10110 = *__petr4_0b10101;
  *__petr4_0b10011 = __petr4_0b10100;
  *__petr4_0b10101 = __petr4_0b10110;
}

void test_verifyChecksum(struct __petr4_0b1000 *__petr4_0b10011, struct __petr4_0b1100 *__petr4_0b10101)
{
  struct __petr4_0b1100 __petr4_0b10110;
  struct __petr4_0b1000 __petr4_0b10100;
  __petr4_0b10100 = *__petr4_0b10011;
  __petr4_0b10110 = *__petr4_0b10101;
  *__petr4_0b10011 = __petr4_0b10100;
  *__petr4_0b10101 = __petr4_0b10110;
}

void MyParser(void *__petr4_0b110, struct __petr4_0b1000 *__petr4_0b111, struct __petr4_0b1100 *__petr4_0b1011, struct __petr4_0b10000 *__petr4_0b1111)
{
  struct __petr4_0b10000 __petr4_0b10010;
  struct __petr4_0b1100 __petr4_0b1110;
  struct __petr4_0b1000 __petr4_0b1010;
  __petr4_0b1010 = *__petr4_0b111;
  __petr4_0b1110 = *__petr4_0b1011;
  __petr4_0b10010 = *__petr4_0b1111;
  start(&__petr4_0b1010, &__petr4_0b1110, &__petr4_0b10010);
  *__petr4_0b111 = __petr4_0b1010;
  *__petr4_0b1011 = __petr4_0b1110;
  *__petr4_0b1111 = __petr4_0b10010;
}

void start(void *__petr4_0b110, struct __petr4_0b1000 *__petr4_0b111, struct __petr4_0b1100 *__petr4_0b1011, struct __petr4_0b10000 *__petr4_0b1111)
{
  /*skip*/;
  return;
}


