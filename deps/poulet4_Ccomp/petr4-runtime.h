#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <gmp.h>
#include <assert.h>
#include <math.h> 

typedef void *$pkt_in;
typedef void *$pkt_out;

typedef struct BitVec {
  //1 = signed, 0 = unsigned 
  int is_signed;

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
  PlusSat,
  Minus,
  MinusSat, 
  Mul,
  Div,
  Mod,
  Shl,
  Shr,
  BitAnd,
  BitXor,
  BitOr
};

/**
Functions: includes package processing, unary operations, and binary operations 
**/

//package processing
void extract($pkt_in pkt, void *data, int len);
void emit($pkt_out pkt, void *data, int len);

//unary operators
void eval_uminus(mpz_t v) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  mpz_neg(dst_value, v);
}

//binary operators
//is_add = 1 --> add, is_add = -1 --> subtract 
void eval_sat_add_sub(struct BitVec *dst, struct BitVec l, struct BitVec r, int is_add) {
  if (l.is_signed == 1 && r.is_signed == 1) {
    mpz_mul(r.value, r.value, is_add);
    mpz_add(dst->value, l.value, r.value);
    mpz_mod_ui(dst->value, dst->value, dst->width);
  }
  else {
    mpz_mul(r.value, r.value, is_add);
    dst->is_signed = 1; 
    mpz_add(dst->value, l.value, r.value);
    mpz_mod_ui(dst->value, dst->value, pow(2, dst->width)-1);
  }
}

void interp_binary_op(enum operation op, struct BitVec l, struct BitVec r) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  struct BitVec dst = { 0,
                        l.width, //assumption: width of l and r are =
                        dst_value };

  switch (op) {
    case Plus:
      mpz_add(dst.value, l.value, r.value);
      mpz_mod_ui(dst.value, dst.value, dst.width);
    case PlusSat:
      eval_sat_add_sub(&dst, l, r, 1);
    case Minus:
      mpz_sub(dst.value, l.value, r.value);
      mpz_mod_ui(dst.value, dst.value, dst.width);
    case MinusSat:
      eval_sat_add_sub(&dst, l, r, -1);
    case Mul:
      mpz_mul(dst.value, l.value, r.value);
      mpz_mod_ui(dst.value, dst.value, dst.width);
    case Div: 
      mpz_cdiv_q(dst.value, l.value, r.value);
      mpz_mod_ui(dst.value, dst.value, dst.width);
    case Mod:
      mpz_mod(dst.value, l.value, r.value);
    case Shl:
      mpz_mul_2exp(dst.value, l.value, r.value);
    case Shr:
      //For positive n both mpz_fdiv_q_2exp and mpz_tdiv_q_2exp are simple bitwise right shifts. For negative n, mpz_fdiv_q_2exp is effectively an arithmetic right shift treating n as twos complement the same as the bitwise logical functions do, whereas mpz_tdiv_q_2exp effectively treats n as sign and magnitude.
      if(dst.is_signed) { //might want to fix this condition 
        mpz_fdiv_q_2exp(dst.value, l.value, r.value); 
      } 
      else {
        mpz_tdiv_q_2exp(dst.value, l.value, r.value);
      }
    case BitAnd:
      mpz_and(dst.value, l.value, r.value);
    case BitXor:
      mpz_xor(dst.value, l.value, r.value); 
    case BitOr:
      mpz_ior(dst.value, l.value, r.value); 
    default:
      ;
  };
}
