#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <gmp.h>
#include <assert.h>
#include <math.h> 

typedef void *$pkt_in;
typedef void *$pkt_out;
typedef void *$BitVec;

struct BitVec
{
  //True = signed, False = unsigned 
  bool signed;

  //representation of the binary width of the number representation of the bit_vec
  int width;

  //the GMP representation of the number. 
  //0<=value<=2^width-1 
  mpz_t value; 
};

void reset_bitvec (mpz_t x) {
  mpz_clear(x);
}

enum operation{
  Plus,
  PlusSat 
  Mul
};

/**
Functions: includes package processing, unary operations, and binary operations 
**/

//package processing
void extract($pkt_in pkt, void *data, int len);
void emit($pkt_out pkt, void *data, int len);

//unary operators
void eval_uminus($BitVec v, $BitVec dst) {
  init_bitvec(v.input, n);
  mpz_neg(n, v_bitvec);
  dst = bit_vec(mpz_get_str(NULL, 10, n));
  reset_bitvec(n); 
}

//binary operators
void eval_sat_add(mpz_t dst_value, const mpz_t l_value, const mpz_t r_value) {
  switch (l.signed, r.signed):
    case (True, True):
      mpz_add(dst_value, l_value, r_value);
      mpz_mod(dst.value, dst.value, dst.width);
    default:
      dst.signed = True; 
      mpz_add(dst_value, l_value, r_value);
      mpz_mod(dst.value, dst.value, pow(2, dst.width)-1);
}

void interp_binary_op(operation op, $BitVec l, $BitVec r) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  struct BitVec dst = { .signed = False,
                        .width = l.width, //assumption: width of l and r are =
                        .value = dst_value }

  switch (op):
    case Plus:
      mpz_add(dst.value, l.value, r.value);
      mpz_mod(dst.value, dst.value, dst.width);
    case PlusSat:
      eval_sat_add(dst.value, l.value, r.value);
    case Mul:
      mpz_mul(dst.value, l.value, r.value);
      mpz_mod(dst.value, dst.value, dst.width);
    default:
      failwith("unimplemented")
}
