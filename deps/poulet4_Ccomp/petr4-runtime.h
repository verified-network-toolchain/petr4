// Need to expose GMP operations for each P4 construct

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef void *$1;//packet in
typedef void *$2;//packet out
typedef void *$3;//bit vec

void extract($1 pkt, void *data, int len);
void emit($2 pkt, void *data, int len);

struct bit_vec
{
  //define with gmp
  //width
  //sign
};

//unary operators
//always know the width because you can extract it from the type
void eval_bitnot($3 v, $3 dst);
void eval_uminus($3 v, $3 dst);

//binary operators
// check that params have the same type -
void unsigned_plus($3 l, $3 r, $3 dst);
void signed_plus($3 l, $3 r, $3 dst);
$3 interp_bplus($3 l, $3 r);