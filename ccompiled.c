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

extern unsigned int __compcert_va_int32(void *);
extern unsigned long long __compcert_va_int64(void *);
extern double __compcert_va_float64(void *);
extern void *__compcert_va_composite(void *, unsigned long long);
extern long long __compcert_i64_dtos(double);
extern unsigned long long __compcert_i64_dtou(double);
extern double __compcert_i64_stod(long long);
extern double __compcert_i64_utod(unsigned long long);
extern float __compcert_i64_stof(long long);
extern float __compcert_i64_utof(unsigned long long);
extern long long __compcert_i64_sdiv(long long, long long);
extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);
extern long long __compcert_i64_smod(long long, long long);
extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);
extern long long __compcert_i64_shl(long long, int);
extern unsigned long long __compcert_i64_shr(unsigned long long, int);
extern long long __compcert_i64_sar(long long, int);
extern long long __compcert_i64_smulh(long long, long long);
extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);
extern void __builtin_debug(int, ...);
extern void __gmpz_add(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_and(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_cdiv_q(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_clear(struct _585 *);
extern int __gmpz_cmp(struct _585 *, struct _585 *);
extern int __gmpz_cmp_d(struct _585 *, double);
extern void __gmpz_fdiv_q_2exp(struct _585 *, struct _585 *, unsigned long long);
extern unsigned long long __gmpz_fdiv_r_ui(struct _585 *, struct _585 *, unsigned long long);
extern void __gmpz_init(struct _585 *);
extern void __gmpz_ior(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_mod(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_mul(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_mul_2exp(struct _585 *, struct _585 *, unsigned long long);
extern void __gmpz_neg(struct _585 *, struct _585 *);
extern void __gmpz_set_ui(struct _585 *, unsigned long long);
extern void __gmpz_sub(struct _585 *, struct _585 *, struct _585 *);
extern void __gmpz_tdiv_q_2exp(struct _585 *, struct _585 *, unsigned long long);
extern void __gmpz_xor(struct _585 *, struct _585 *, struct _585 *);
extern double pow(double, double);
void reset_bitvec(struct _585 *);
void eval_uminus(struct _585 *);
void eval_sat_add_sub(struct BitVec *, struct BitVec, struct BitVec, int);
void init_interp_binary_op(struct BitVec *, struct BitVec);
void eval_plus(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_plus_sat(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_minus(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_minus_sat(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_mul(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_div(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_mod(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_shl(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_shr(struct BitVec *, int, struct BitVec, struct BitVec);
int eval_le(int, struct BitVec, struct BitVec);
int eval_ge(int, struct BitVec, struct BitVec);
int eval_lt(int, struct BitVec, struct BitVec);
int eval_gt(int, struct BitVec, struct BitVec);
int eval_eq(int, struct BitVec, struct BitVec);
int eval_not_eq(int, struct BitVec, struct BitVec);
void eval_bitand(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_bitxor(struct BitVec *, int, struct BitVec, struct BitVec);
void eval_bitor(struct BitVec *, int, struct BitVec, struct BitVec);
int eval_and(int, struct BitVec, struct BitVec);
int eval_or(int, struct BitVec, struct BitVec);
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
void reset_bitvec(struct _585 *x)
{
  __gmpz_clear(x);
}

void eval_uminus(struct _585 *v)
{
  struct _585 dst_value[1];
  __gmpz_init(dst_value);
  __gmpz_set_ui(dst_value, 0);
  __gmpz_neg(dst_value, v);
}

void eval_sat_add_sub(struct BitVec *dst, struct BitVec l, struct BitVec r, int is_add)
{
  struct BitVec l;
  struct BitVec r;
  register int 1;
  register double 0;
  l = l;
  r = r;
  if (l.is_signed == 1) {
    1 = (_Bool) (r.is_signed == 1);
  } else {
    1 = 0;
  }
  if (1) {
    __gmpz_mul(r.value, r.value, is_add);
    __gmpz_add((*dst).value, l.value, r.value);
    __gmpz_fdiv_r_ui((*dst).value, (*dst).value, (*dst).width);
  } else {
    __gmpz_mul(r.value, r.value, is_add);
    (*dst).is_signed = 1;
    __gmpz_add((*dst).value, l.value, r.value);
    0 = pow(2, (*dst).width);
    __gmpz_fdiv_r_ui((*dst).value, (*dst).value, 0 - 1);
  }
}

void init_interp_binary_op(struct BitVec *_res, struct BitVec l)
{
  struct BitVec l;
  struct _585 dst_value[1];
  struct BitVec dst;
  l = l;
  __gmpz_init(dst_value);
  __gmpz_set_ui(dst_value, 0);
  dst.is_signed = 0;
  dst.width = l.width;
  (*(dst.value + 0))._mp_alloc = dst_value;
  (*(dst.value + 0))._mp_size = 0;
  (*(dst.value + 0))._mp_d = (void *) 0;
  *_res = dst;
  return;
}

void eval_plus(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_add(dst.value, l.value, r.value);
  __gmpz_fdiv_r_ui(dst.value, dst.value, dst.width);
  *_res = dst;
  return;
}

void eval_plus_sat(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  eval_sat_add_sub(&dst, l, r, 1);
  *_res = dst;
  return;
}

void eval_minus(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_sub(dst.value, l.value, r.value);
  __gmpz_fdiv_r_ui(dst.value, dst.value, dst.width);
  *_res = dst;
  return;
}

void eval_minus_sat(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  eval_sat_add_sub(&dst, l, r, -1);
  *_res = dst;
  return;
}

void eval_mul(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_mul(dst.value, l.value, r.value);
  __gmpz_fdiv_r_ui(dst.value, dst.value, dst.width);
  *_res = dst;
  return;
}

void eval_div(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_cdiv_q(dst.value, l.value, r.value);
  __gmpz_fdiv_r_ui(dst.value, dst.value, dst.width);
  *_res = dst;
  return;
}

void eval_mod(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_mod(dst.value, l.value, r.value);
  *_res = dst;
  return;
}

void eval_shl(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_mul_2exp(dst.value, l.value, r.value);
  *_res = dst;
  return;
}

void eval_shr(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  if (dst.is_signed) {
    __gmpz_fdiv_q_2exp(dst.value, l.value, r.value);
  } else {
    __gmpz_tdiv_q_2exp(dst.value, l.value, r.value);
  }
}

int eval_le(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 <= 0) {
    return 1;
  }
  return 0;
}

int eval_ge(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 >= 0) {
    return 1;
  }
  return 0;
}

int eval_lt(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 < 0) {
    return 1;
  }
  return 0;
}

int eval_gt(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 > 0) {
    return 1;
  }
  return 0;
}

int eval_eq(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 == 0) {
    return 1;
  }
  return 0;
}

int eval_not_eq(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp(l.value, r.value);
  if (0 != 0) {
    return 1;
  }
  return 0;
}

void eval_bitand(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_and(dst.value, l.value, r.value);
  *_res = dst;
  return;
}

void eval_bitxor(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_xor(dst.value, l.value, r.value);
  *_res = dst;
  return;
}

void eval_bitor(struct BitVec *_res, int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res__1;
  l = l;
  r = r;
  init_interp_binary_op(&_res__1, l);
  dst = _res__1;
  __gmpz_ior(dst.value, l.value, r.value);
  *_res = dst;
  return;
}

int eval_and(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 2;
  register int 1;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp_d(l.value, 0);
  if (0 != 0) {
    1 = 1;
  } else {
    2 = __gmpz_cmp_d(r.value, 0);
    1 = (_Bool) (2 != 0);
  }
  if (1) {
    return 1;
  }
  return 0;
}

int eval_or(int op, struct BitVec l, struct BitVec r)
{
  struct BitVec l;
  struct BitVec r;
  struct BitVec dst;
  struct BitVec _res;
  register int 2;
  register int 1;
  register int 0;
  l = l;
  r = r;
  init_interp_binary_op(&_res, l);
  dst = _res;
  0 = __gmpz_cmp_d(l.value, 0);
  if (0 != 0) {
    2 = __gmpz_cmp_d(r.value, 0);
    1 = (_Bool) (2 != 0);
  } else {
    1 = 0;
  }
  if (1) {
    return 1;
  }
  return 0;
}

void __petr4_0b101(void)
{
  struct  __petr4_0b110010;
  struct  __petr4_0b110001;
  struct __petr4_0b10000 *__petr4_0b110000;
  struct __petr4_0b1100 *__petr4_0b101111;
  struct __petr4_0b1000 *__petr4_0b101110;
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


