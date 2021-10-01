struct __petr4_0b1011;
struct __petr4_0b111;
struct __petr4_0b11;
struct __petr4_0b1011 {
  _Bool __petr4_0b1100;
};

struct __petr4_0b111 {
  _Bool __petr4_0b1000;
};

struct __petr4_0b11 {
  _Bool __petr4_0b100;
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
int main(void)
{
  struct packet_in __petr4_0b101001;
  struct packet_in __petr4_0b101000;
  struct __petr4_0b1011 __petr4_0b100111;
  struct __petr4_0b111 __petr4_0b100110;
  struct __petr4_0b11 __petr4_0b100101;
  MyParser
    (__petr4_0b101000, &__petr4_0b100101, &__petr4_0b100110,
     &__petr4_0b100111);
  MyVerifyChecksum(&__petr4_0b100101, &__petr4_0b100110);
  MyIngress(&__petr4_0b100101, &__petr4_0b100110, &__petr4_0b100111);
  MyEgress(&__petr4_0b100101, &__petr4_0b100110, &__petr4_0b100111);
  MyComputeChecksum(&__petr4_0b100101, &__petr4_0b100110);
  MyDeparser(__petr4_0b101001, __petr4_0b100101);
}

void MyDeparser(struct packet_out __petr4_0b100010, struct __petr4_0b11 __petr4_0b100011)
{
  struct __petr4_0b11 __petr4_0b100100;
  __petr4_0b100100 = __petr4_0b100011;
  __petr4_0b100011 = __petr4_0b100100;
}

void test_deparser(struct packet_out __petr4_0b100010, struct __petr4_0b11 __petr4_0b100011)
{
  struct __petr4_0b11 __petr4_0b100100;
  __petr4_0b100100 = __petr4_0b100011;
  __petr4_0b100011 = __petr4_0b100100;
}

void MyComputeChecksum(struct __petr4_0b11 *__petr4_0b11110, struct __petr4_0b111 *__petr4_0b100000)
{
  struct __petr4_0b111 __petr4_0b100001;
  struct __petr4_0b11 __petr4_0b11111;
  __petr4_0b11111 = *__petr4_0b11110;
  __petr4_0b100001 = *__petr4_0b100000;
  *__petr4_0b11110 = __petr4_0b11111;
  *__petr4_0b100000 = __petr4_0b100001;
}

void test_computeChecksum(struct __petr4_0b11 *__petr4_0b11110, struct __petr4_0b111 *__petr4_0b100000)
{
  struct __petr4_0b111 __petr4_0b100001;
  struct __petr4_0b11 __petr4_0b11111;
  __petr4_0b11111 = *__petr4_0b11110;
  __petr4_0b100001 = *__petr4_0b100000;
  *__petr4_0b11110 = __petr4_0b11111;
  *__petr4_0b100000 = __petr4_0b100001;
}

void MyEgress(struct __petr4_0b11 *__petr4_0b11000, struct __petr4_0b111 *__petr4_0b11010, struct __petr4_0b1011 *__petr4_0b11100)
{
  struct __petr4_0b1011 __petr4_0b11101;
  struct __petr4_0b111 __petr4_0b11011;
  struct __petr4_0b11 __petr4_0b11001;
  __petr4_0b11001 = *__petr4_0b11000;
  __petr4_0b11011 = *__petr4_0b11010;
  __petr4_0b11101 = *__petr4_0b11100;
  *__petr4_0b11000 = __petr4_0b11001;
  *__petr4_0b11010 = __petr4_0b11011;
  *__petr4_0b11100 = __petr4_0b11101;
}

void test_egress(struct __petr4_0b11 *__petr4_0b11000, struct __petr4_0b111 *__petr4_0b11010, struct __petr4_0b1011 *__petr4_0b11100)
{
  struct __petr4_0b1011 __petr4_0b11101;
  struct __petr4_0b111 __petr4_0b11011;
  struct __petr4_0b11 __petr4_0b11001;
  __petr4_0b11001 = *__petr4_0b11000;
  __petr4_0b11011 = *__petr4_0b11010;
  __petr4_0b11101 = *__petr4_0b11100;
  *__petr4_0b11000 = __petr4_0b11001;
  *__petr4_0b11010 = __petr4_0b11011;
  *__petr4_0b11100 = __petr4_0b11101;
}

void MyIngress(struct __petr4_0b11 *__petr4_0b10010, struct __petr4_0b111 *__petr4_0b10100, struct __petr4_0b1011 *__petr4_0b10110)
{
  struct __petr4_0b1011 __petr4_0b10111;
  struct __petr4_0b111 __petr4_0b10101;
  struct __petr4_0b11 __petr4_0b10011;
  __petr4_0b10011 = *__petr4_0b10010;
  __petr4_0b10101 = *__petr4_0b10100;
  __petr4_0b10111 = *__petr4_0b10110;
  *__petr4_0b10010 = __petr4_0b10011;
  *__petr4_0b10100 = __petr4_0b10101;
  *__petr4_0b10110 = __petr4_0b10111;
}

void test_ingress(struct __petr4_0b11 *__petr4_0b10010, struct __petr4_0b111 *__petr4_0b10100, struct __petr4_0b1011 *__petr4_0b10110)
{
  struct __petr4_0b1011 __petr4_0b10111;
  struct __petr4_0b111 __petr4_0b10101;
  struct __petr4_0b11 __petr4_0b10011;
  __petr4_0b10011 = *__petr4_0b10010;
  __petr4_0b10101 = *__petr4_0b10100;
  __petr4_0b10111 = *__petr4_0b10110;
  *__petr4_0b10010 = __petr4_0b10011;
  *__petr4_0b10100 = __petr4_0b10101;
  *__petr4_0b10110 = __petr4_0b10111;
}

void MyVerifyChecksum(struct __petr4_0b11 *__petr4_0b1110, struct __petr4_0b111 *__petr4_0b10000)
{
  struct __petr4_0b111 __petr4_0b10001;
  struct __petr4_0b11 __petr4_0b1111;
  __petr4_0b1111 = *__petr4_0b1110;
  __petr4_0b10001 = *__petr4_0b10000;
  *__petr4_0b1110 = __petr4_0b1111;
  *__petr4_0b10000 = __petr4_0b10001;
}

void test_verifyChecksum(struct __petr4_0b11 *__petr4_0b1110, struct __petr4_0b111 *__petr4_0b10000)
{
  struct __petr4_0b111 __petr4_0b10001;
  struct __petr4_0b11 __petr4_0b1111;
  __petr4_0b1111 = *__petr4_0b1110;
  __petr4_0b10001 = *__petr4_0b10000;
  *__petr4_0b1110 = __petr4_0b1111;
  *__petr4_0b10000 = __petr4_0b10001;
}

void MyParser(struct packet_in __petr4_0b1, struct __petr4_0b11 *__petr4_0b10, struct __petr4_0b111 *__petr4_0b110, struct __petr4_0b1011 *__petr4_0b1010)
{
  struct __petr4_0b1011 __petr4_0b1101;
  struct __petr4_0b111 __petr4_0b1001;
  struct __petr4_0b11 __petr4_0b101;
  __petr4_0b101 = *__petr4_0b10;
  __petr4_0b1001 = *__petr4_0b110;
  __petr4_0b1101 = *__petr4_0b1010;
  start(&__petr4_0b101, &__petr4_0b1001, &__petr4_0b1101);
  *__petr4_0b10 = __petr4_0b101;
  *__petr4_0b110 = __petr4_0b1001;
  *__petr4_0b1010 = __petr4_0b1101;
}

void start(struct packet_in __petr4_0b1, struct __petr4_0b11 *__petr4_0b10, struct __petr4_0b111 *__petr4_0b110, struct __petr4_0b1011 *__petr4_0b1010)
{
  /*skip*/;
  return;
}


