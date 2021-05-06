// Need to expose GMP operations for each P4 construct

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef char bool;
#define true 1
#define false 0

typedef char bit8;

typedef void *packet_in;
typedef void *packet_out;

void extract(packet_in pkt, void *data, int len);
void emit(packet_out pkt, void *data, int len);

struct bit_vec
{
  //define with gmp
  //width
  //sign
};

//unary operators
//always know the width because you can extract it from the type
bool eval_not(bool v);
bit_vec eval_bitnot(bit_vec v);
bit_vec eval_uminus(bit_vec v);

//binary operators
// check that params have the same type -
bit_vec unsigned_op_sat(bit_vec l, bit_vec r, bit_vec (*op)(bit_vec, bit_vec));
bit_vec signed_op_sat(bit_vec l, bit_vec r, bit_vec (*op)(bit_vec, bit_vec));
bit_vec interp_bplus(bit_vec l, bit_vec r);
