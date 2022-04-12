#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gmp.h"
#include <assert.h>
#include <math.h> 

enum p4int {FIXBIT, FIXINT};



typedef struct packet_in {
  unsigned char *in; //currently, we just use the last bit of the 8 bits.
} packet_in;

typedef struct packet_out{
  unsigned char *out;
  unsigned char *index;
} packet_out;

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

  mpz_init(dst->value);
  mpz_set(dst->value, i); 
  dst->is_signed = sign;
  dst->width = w;
}

void init_bitvec_ptr(struct BitVec **dst, int sign, int w, char *val){
  BitVec * bv = malloc(sizeof(BitVec));
  mpz_t i;
  int check;

  mpz_init(i);
  mpz_set_ui(i,0);

  check = mpz_set_str(i,val, 10);
  assert (check == 0); 

  mpz_init(bv->value);
  mpz_set(bv->value, i); 
  bv->is_signed = sign;
  bv->width = w;
  *dst = bv;
}

/**
 * sign = 0 means unsigned, = 1 means signed
 * w is the width
 * val is the decimal string of the value.
 * 
 * */
void init_bitvec_binary(struct BitVec *dst, int sign, int w, char *val){
  mpz_t i;
  int check;

  mpz_init(i);
  mpz_set_ui(i,0);

  check = mpz_set_str(i,val, 2);
  assert (check == 0); 

  mpz_init(dst->value);
  mpz_set(dst->value, i); 
  dst->is_signed = sign;
  dst->width = w;
}

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

//v1model externs
BitVec drop_port; 
void mark_to_drop(struct standard_metadata_t* meta){
  init_bitvec(&drop_port, 0, 9, "511");
  *(meta->egress_spec) = drop_port;
}

//packet processing
void extract_bool(packet_in *pkt, int *data){
  if(*(pkt->in) - 48 == 1){//input is '0' or '1'
    *data = 1;
  } else {
    *data = 0;
  }
  pkt->in ++;
}

void extract_bitvec(packet_in *pkt, BitVec *data, int is_signed, int width){
  char* val = (char *) malloc(sizeof (char) * width); 
  for(int i = 0; i < width; i++){
    val[i] = (*(pkt->in)); //we expect the input to be '1' or '0', gmp uses string to initialize the integer.
    pkt->in ++;
  }
  init_bitvec_binary(data, is_signed, width, val);
}


void emit_bool(packet_out *pkt, int *data){
  *(pkt->index) = *data + 48;
  pkt->index ++;
}

void emit_bitvec(packet_out *pkt, BitVec *data){
  int size = mpz_sizeinbase (data->value, 2) + 2;
  char* val = malloc(sizeof(char) * size);
  mpz_get_str(val, 2, data->value);
  for(int i = 0; i< data->width; i++){
    if(data->width - size > i){
      *(pkt->index) = '0';
    }else{
      *(pkt->index) = val[i - (data->width - size)];
    }
    pkt->index ++;
  }
}


//unary operators
void eval_uminus(mpz_t v) {
  mpz_t dst_value;
  mpz_init(dst_value);
  mpz_set_ui(dst_value, 0);
  mpz_neg(dst_value, v);
}

void interp_uminus(BitVec *dst, BitVec src){
  dst->width = src.width;
  dst->is_signed = src.is_signed;
  mpz_init(dst->value);
  if(src.is_signed){
    mpz_neg(dst->value, src.value);
    mpz_t top;
    mpz_init(top);
    mpz_ui_pow_ui(top, 2, src.width-1);
    if(mpz_cmp(dst->value,top)==0){
      mpz_set(dst->value, src.value);
    }
  }else{
    mpz_t top;
    mpz_init(top);
    mpz_ui_pow_ui(top, 2, src.width);
    mpz_sub(dst->value, top, src.value);
  }
}


//binary operators

//helpers
//is_add = 1 --> add, is_add = -1 --> subtract 
void eval_sat_add_sub(struct BitVec *dst, struct BitVec l, struct BitVec r, int is_add) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_t min;
  mpz_t max;
  mpz_init(min);
  mpz_init(max);
  if (l.is_signed == 1 && r.is_signed == 1) {
    //signed, min = -2^{width-1}, max = 2^{width-1} - 1
    mpz_ui_pow_ui(min, 2, (l.width - 1));
    mpz_neg (min,min);
    mpz_ui_pow_ui(max, 2, (l.width-1));
    mpz_sub_ui(max, max, 1);

  }
  else {
    //signed, min = 0, max = 2^{width} - 1
    mpz_set_ui(min, 0);
    mpz_neg (min,min);
    mpz_ui_pow_ui(max, 2, l.width);
    mpz_sub_ui(max, max, 1);
    
  }
  //arithmetic
  mpz_mul(r.value, r.value, is_add);
  mpz_add(dst->value, l.value, r.value);

  //saturation
  if(mpz_cmp(dst->value, min) < 0){
    mpz_set(dst->value, min);
  }else if(mpz_cmp(dst->value,max) > 0){
    mpz_set(dst->value, max);
  }

}

void wrap_around(BitVec* dst){
  mpz_t min;
  mpz_t max;
  mpz_init(min);
  mpz_init(max);

  //signed, min = -2^{width-1}, max = 2^{width-1} - 1
  mpz_ui_pow_ui(min, 2, (dst->width - 1));
  mpz_neg (min,min);
  mpz_ui_pow_ui(max, 2, (dst->width-1));
  mpz_sub_ui(max, max, 1);

  //wrap around if exceed.
  if(mpz_cmp(dst->value, max)>0){
    mpz_sub(dst->value, dst->value, max);
    mpz_add(dst->value, dst->value, min);
  }
  if(mpz_cmp(dst->value, min) < 0){
    mpz_sub(dst->value, dst->value, min);
    mpz_add(dst->value, dst->value, max);
  }
}

// struct BitVec init_interp_binary_op(struct BitVec l) {
//   mpz_t dst_value;
//   mpz_init(dst_value);
//   mpz_set_ui(dst_value, 0);
//   struct BitVec dst = { 0,
//                         l.width, //assumption: width of l and r are =
//                         dst_value };
//   return dst; 
// }

//main functions

void interp_bplus(BitVec* dst, BitVec l, BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  if(l.is_signed){
    mpz_add(dst->value, l.value, r.value);
    wrap_around(dst);
  }else{
    mpz_t top;
    mpz_init(top);
    mpz_ui_pow_ui(top, 2, dst->width);
    mpz_add(dst->value, l.value, r.value);
    mpz_mod(dst->value, dst->value, top);
  }

}

void interp_bplus_sat(BitVec* dst, BitVec l, struct BitVec r) {
  eval_sat_add_sub(dst, l, r, 1); 
}

void interp_bminus(BitVec* dst, BitVec l, BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  if(l.is_signed){
    mpz_sub(dst->value, l.value, r.value);
    wrap_around(dst);
  }else{
    mpz_t top;
    mpz_init(top);
    mpz_ui_pow_ui(top, 2, r.width);
    mpz_sub(dst->value, top, r.value);
    mpz_add(dst->value, dst->value, l.value);
    mpz_mod(dst->value, dst->value, top); 
  }
  
}

void interp_bminus_sat(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  eval_sat_add_sub(dst, l, r, -1); 
}

void interp_bmult(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_mul(dst->value, l.value, r.value);
  mpz_t top;
  mpz_init(top);
  mpz_ui_pow_ui(top, 2, l.width);
  mpz_mod(dst->value, dst->value, top);
  if(dst->is_signed){
    wrap_around(dst);
  }
}

//No division in P4

// void interp_bdiv(struct BitVec* dst, struct BitVec l, struct BitVec r) {
//   mpz_cdiv_q(dst->value, l.value, r.value);
//   mpz_mod_ui(dst->value, dst->value, dst->width); 
// }

void interp_bmod(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_mod(dst->value, l.value, r.value);
}

void interp_bshl(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_mul_2exp(dst->value, l.value, r.value);
}

void interp_bshr(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  //For positive n both mpz_fdiv_q_2exp and mpz_tdiv_q_2exp are simple bitwise right shifts. 
  //For negative n, mpz_fdiv_q_2exp is effectively an arithmetic right shift 
  //treating n as twos complement the same as the bitwise logical functions 
  //do, whereas mpz_tdiv_q_2exp effectively treats n as sign and magnitude.
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_fdiv_q_2exp(dst->value, l.value, r.value); 
}

//1 = true, 0 = false
void interp_ble(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) <= 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

//1 = true, 0 = false
void interp_bge(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) >= 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

//1 = true, 0 = false
void interp_blt(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) < 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

//1 = true, 0 = false
void interp_bgt(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) > 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

//1 = true, 0 = false
void interp_beq(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) == 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

//1 = true, 0 = false
void interp_bne(int* dst, struct BitVec l, struct BitVec r) {
  if (mpz_cmp(l.value, r.value) != 0) {
    *dst = 1;
  } else {
    *dst = 0;
  } 
}

void interp_bitwise_and(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_and(dst->value, l.value, r.value); 
}

void interp_bitwise_xor(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_xor(dst->value, l.value, r.value);  
}

void interp_bitwise_or(struct BitVec* dst, struct BitVec l, struct BitVec r) {
  mpz_init(dst->value);
  dst->width = l.width;
  dst->is_signed = l.is_signed;
  mpz_ior(dst->value, l.value, r.value); 
}

// //1 = true, 0 = false
// int interp_band(struct BitVec* dst, struct BitVec l, struct BitVec r) {
//   if (mpz_cmp_d(l.value, 0.0) != 0 ||  mpz_cmp_d(r.value, 0.0) != 0) {
//     return 1;
//   } 
//   return 0; 
// }

// //1 = true, 0 = false
// int interp_bor(struct BitVec* dst, struct BitVec l, struct BitVec r) {
//   if (mpz_cmp_d(l.value, 0.0) != 0 &&  mpz_cmp_d(r.value, 0.0) != 0) {
//     return 1;
//   } 
//   return 0; 
// }

void interp_concat(BitVec* dst, BitVec l, BitVec r){
  dst->width = l.width + r.width;
  dst->is_signed = l.is_signed;
  mpz_t left_shifted;
  mpz_init(left_shifted);
  mpz_mul_2exp(left_shifted, l.value,  (long unsigned int)r.width);
  mpz_add(dst->value, left_shifted, r.value);
}

void interp_cast_to_bool(int* dst, BitVec src){ 
  *dst = mpz_cmp_si(src.value, (long)0);
}

void interp_cast_from_bool(BitVec* dst, int src){
  dst->width = 1;
  dst->is_signed = 0;
  mpz_init(dst->value);
  mpz_set_si(dst->value, (long)src);
}

void interp_cast(BitVec* dst, BitVec src, int t, int width){
  dst->width = width;
  if(t == FIXBIT){
    dst->is_signed = 0;
    mpz_init(dst->value);
    if (src.is_signed){
      if(mpz_cmp_si(src.value, (long)0) < 0){
        mpz_t top;
        mpz_init(top);
        mpz_ui_pow_ui(top, 2, dst->width);
        mpz_add(dst->value, src.value, top);
      } else {
        mpz_set(dst->value, src.value);
      }
    }else{
      if(src.width > width){
        mpz_t top;
        mpz_init(top);
        mpz_ui_pow_ui(top, 2, dst->width);
        mpz_mod(dst->value, src.value, top);
      } else {
        mpz_set(dst->value, src.value);
      }
    }
  }else {
    dst->is_signed = 1;
    mpz_init(dst->value);
    if(src.is_signed){
      if(src.width > width){
        mpz_t top;
        mpz_init(top);
        mpz_ui_pow_ui(top, 2, width);
        mpz_mod(dst->value, src.value, top);
        wrap_around(dst);
      }else {
        mpz_set(dst->value, src.value);
      }
    }
  }
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
Table* init_table(int num_keys, int size){
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

