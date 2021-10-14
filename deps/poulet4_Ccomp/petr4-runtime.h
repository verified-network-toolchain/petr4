#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gmp.h"
#include <assert.h>
#include <math.h> 


struct packet_in {
  void *in;
};
struct packet_out{
  void *out;
};

struct BitVec{
  //1 = signed, 0 = unsigned 
  int is_signed;

  //representation of the binary width of the number representation of the bit_vec
  int width;

  //the GMP representation of the number. 
  //0<=value<=2^width-1 
  mpz_t value; 
};

struct TableKey{
  struct BitVec val;
  int match_bits;
  //TODO: add support for ternary
};

struct Table{
  int num_keys;
  int num_entries;
  //array of matchkinds for the keys
  //1 = exact. TODO: 2 = lpm, 3 = ternary
  int* matchkind;
  //keys and their corresponding actions
  struct TableKey** keys;
  int* actions;
  //0 = invalid, 1 = valid.
  int* valid;
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
void extract(struct packet_in pkt, void *data, int len);
void emit(struct packet_out pkt, void *data, int len);

/**
 * sign = 0 means unsigned, = 1 means signed
 * w is the width
 * val is the decimal string of the value.
 * 
 * */
void init_bitvec(struct BitVec *dst, int sign, int w, char *val){
  mpz_t i;
  int check;

  mpz_init(i);
  mpz_set_ui(i,0);

  check = mpz_set_str(i,val, 10);
  assert (check == 0); 

  mpz_set(dst->value, i); 
}

//unary operators
void eval_uminus(mpz_t v) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  mpz_neg(dst_value, v);
}

//binary operators

//helpers
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
    //pow(2, dst->width)-1 , this used to be the third argument in the line below
    //but pow does not seem to be defined.
    mpz_mod_ui(dst->value, dst->value, (int) pow(2.0, (double)dst->width)-1);
  }
}

struct BitVec init_interp_binary_op(struct BitVec l) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  struct BitVec dst = { 0,
                        l.width, //assumption: width of l and r are =
                        dst_value };
  return dst; 
}

//main functions

void interp_bplus(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_add(dst->value, l.value, r.value);
  mpz_mod_ui(dst->value, dst->value, dst->width);
}

void interp_bplus_sat(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  eval_sat_add_sub(&dst, l, r, 1); 
}

void interp_bminus(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_sub(dst->value, l.value, r.value);
  mpz_mod_ui(dst->value, dst->value, dst->width); 
}

void interp_bminus_sat(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  eval_sat_add_sub(&dst, l, r, -1); 
}

void interp_bmult(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_mul(dst->value, l.value, r.value);
  mpz_mod_ui(dst->value, dst->value, dst->width);
}

void interp_bdiv(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_cdiv_q(dst->value, l.value, r.value);
  mpz_mod_ui(dst->value, dst->value, dst->width); 
}

void interp_bmod(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_mod(dst->value, l.value, r.value);
}

void interp_bshl(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_mul_2exp(dst->value, l.value, r.value);
}

void interp_bshr(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  //For positive n both mpz_fdiv_q_2exp and mpz_tdiv_q_2exp are simple bitwise right shifts. 
  //For negative n, mpz_fdiv_q_2exp is effectively an arithmetic right shift 
  //treating n as twos complement the same as the bitwise logical functions 
  //do, whereas mpz_tdiv_q_2exp effectively treats n as sign and magnitude.
  if(dst->is_signed) { //might want to fix this condition 
    mpz_fdiv_q_2exp(dst->value, l.value, r.value); 
  } 
  else {
    mpz_tdiv_q_2exp(dst->value, l.value, r.value);
  }
}

//1 = true, 0 = false
void interp_ble(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) <= 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

//1 = true, 0 = false
void interp_bge(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) >= 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

//1 = true, 0 = false
void interp_blt(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) < 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

//1 = true, 0 = false
void interp_bgt(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) > 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

//1 = true, 0 = false
void interp_beq(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) == 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

//1 = true, 0 = false
void interp_bne(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) != 0) {
    *dst = 1;
  } 
  *dst = 0; 
}

void interp_bitwise_and(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_and(dst->value, l.value, r.value); 
}

void interp_bitwise_xor(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_xor(dst->value, l.value, r.value);  
}

void interp_bitwise_or(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_ior(dst->value, l.value, r.value); 
}

//1 = true, 0 = false
int interp_band(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp_d(l.value, 0.0) != 0 ||  mpz_cmp_d(r.value, 0.0) != 0) {
    return 1;
  } 
  return 0; 
}

//1 = true, 0 = false
int interp_bor(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp_d(l.value, 0.0) != 0 &&  mpz_cmp_d(r.value, 0.0) != 0) {
    return 1;
  } 
  return 0; 
}

//initialize a table with the given number of keys, the desired size of the table
//and the matchkind of all its keys
void init_table(struct Table* table, int num_key, int size, int* matchkinds){
  table->num_keys = num_key;
  table->num_entries = size;
  table->matchkind = (int*) malloc(sizeof(int) * num_key);
  for(int i = 0; i < num_key; i++){
    table->matchkind[i] = matchkinds[i];
  };
  table->keys = (struct TableKey**) malloc(sizeof(struct TableKey*) * size);
  for(int i = 0; i < size; i++){
    table->keys[i] = (struct TableKey*) malloc(sizeof(struct TableKey) * num_key);
  };
  table->actions = (int*) malloc(sizeof(int) * size);
  table->valid = (int*) malloc(sizeof(int) * size);
  for(int i = 0; i < size; i++){
    table->valid[i] = 0;
  }
}

//add a new entry to the table, find the first invalid entry to replace
//if all entries are valid, the new entry won't be added.
//TODO: support actions arguments.
void add_entry(struct Table* table, struct TableKey* newkeys, int new_action){
  for(int i = 0; i < table->num_entries; i++){
    if(!table->valid[i]){
      for(int j = 0; j < table->num_keys; j++){
        table->keys[i][j] = newkeys[j];
      }
      table->actions[i] = new_action;
      table->valid[i] = 1;
      return;
    }
  }
}

//given an array of values, return the action the table should take.
//0 if it is default action
//in the compiler, when it finds out the expression has type bool, it should
//translate it into a bitvec and then put it in the vals. 
//TODO: support action arguments
//QUESTION: what if the keys have different order?
void table_match(int* dst,struct Table* table, struct BitVec* vals){
  for(int entry = 0; entry < table->num_entries; entry++){
    if(!table->valid[entry]){
      continue;
    }
    int result = 1;
    for(int key = 0; key < table->num_keys; key++){
      switch (table->matchkind[key]){
        case 1:{
          if(result){
            interp_beq(&result, vals[key], table->keys[entry][key].val);
          }
        }
        default:{
          //TODO: implement lpm and ternary
          result = result;
        }
      }
    }
    if(result){
      *dst = table->actions[entry];
    }
  }
  *dst = 0;
}