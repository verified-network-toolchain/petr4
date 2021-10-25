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

typedef struct BitVec{
  //1 = signed, 0 = unsigned 
  int is_signed;

  //representation of the binary width of the number representation of the bit_vec
  int width;

  //the GMP representation of the number. 
  //0<=value<=2^width-1 
  mpz_t value; 
} BitVec;

typedef struct Pat{
  struct BitVec mask; //ternary mask
  struct BitVec val; //value 
} Pat;

typedef struct ActionRef{
  int action;
  struct BitVec* arguments;
  int num_args;
} ActionRef;

ActionRef default_action = {0, NULL, 0};

typedef struct Entry{
  Pat* pattern; // a pattern array.
  //Priority is implicit by the order of the entries in the table
  ActionRef action_ref; //since only one per entry, need not to be statically allocated itself.
} Entry;

typedef struct Table{
  int num_keys;
  int num_entries;
  int capacity;//allocated
  struct Entry* entries;
} Table;

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

//The pattern is a stack variable first, but the array of pattern will live in heap
void init_pattern(Pat* pattern,struct BitVec mask, struct BitVec val){
  pattern->mask = mask;
  pattern->val = val;
}

// Action will be a stack variable first, but the entry it resides in will live in heap
// The arguments itself is first declared in stack, but we will allocate it in heap
void init_action(ActionRef* actionRef, int action, struct BitVec* arguments, int num_args){
  actionRef->action = action;
  actionRef->arguments = (BitVec*) malloc(sizeof(BitVec) * num_args);
  for(int i = 0; i < num_args; i++){
    actionRef->arguments[i] = arguments[i];
  };
  actionRef->num_args = num_args;
}

// Entry will be a stack variable first, but its value will be stored 
// in the entry array which is in heap 
// the pattern array live in stack, but we will transfer it into heap
void init_entry(Entry* entry, Pat* pattern, ActionRef action, int num_keys){
  entry->pattern = (Pat*) malloc(sizeof(Pat) * num_keys);
  for (int i = 0; i < num_keys; i++)
  {
    entry->pattern[i] = pattern[i];
  }
  
  entry->action_ref = action;
}

//initialize a table with the given number of keys, the desired size of the table
//and the matchkind of all its keys
Table* init_table(int num_keys, int size, int args_lub){
  Table* table = (Table* ) malloc(sizeof(Table));
  table->num_keys = num_keys;
  table->capacity = size;
  table->num_entries = 0;
  table->entries = (Entry*) malloc(sizeof(Entry) * size);
}

//Example init table: 
// Table* table = init_table(num_keys, size, args_lub);

//Add a new entry to the table, however, this does not support inserting 
//entry from control plane since the table does not store the numerical 
// priority of each entry. And thus the order of the entry must be guaranteed
// to be correct by the compiler.
void add_entry(struct Table* table, Entry entry){
  table->entries[table->num_entries] = entry;
  table->num_entries++;
}


//Example add entry:
// Pat[m] patterns;
// for (int i = 0; i < m; i++){
//   Bitvec mask;
//   Bitvec val;
//   init_bitvec(&mask, ...);
//   init_bitvec(&val, ...);
//   init_pattern(patterns+i, mask, val);
// }
// ActionRef action;
// BitVec[n] arguments;
// for (int i = 0; i < m; i++){
//   init_bitvec(arguments+i, ...);
// };
// init_action(&action, action, arguments, n);
// Entry entry;
// init_entry(&entry, patterns, action, table->num_keys);
// add_entry(table, entry);

//match a value against a single pattern
void pattern_match(int* dst, Pat pattern, BitVec val){
  BitVec val_masked;
  interp_bitwise_and(&val_masked, val, pattern.mask);
  BitVec key_masked;
  interp_bitwise_and(&key_masked, pattern.val, pattern.mask);
  interp_bne(dst, val_masked, key_masked);
}

//match an array of bitvecs with an entry
void entry_match(int* dst, Entry entry, BitVec* val, int num_keys){
  for(int i = 0; i < num_keys; i++){
    pattern_match(dst, entry.pattern[i], val[i]);
    if(!(*dst)){
      return;
    }
  }
}

//given an array of values, return the action the table should take.
//0 if it is default action
//in the compiler, when it finds out the expression has type bool, it should
//translate it into a bitvec and then put it in the vals. 
void table_match(ActionRef* dst, struct Table* table, struct BitVec* keys){
  *dst = default_action;
  for (int i = table->num_entries-1; i>= 0; i--){
    int matched;
    entry_match(&matched, table->entries[i],keys, table->num_keys);
    if(matched){
      *dst = table->entries[i].action_ref;
      return;
    }
  }
}