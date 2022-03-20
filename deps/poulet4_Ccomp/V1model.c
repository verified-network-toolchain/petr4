#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gmp.h"
#include <assert.h>
#include <math.h> 
#include "compiled.c"
// typedef struct Register {
//     int size;
//     void** vals;
// } Register;



// typedef struct State {
//   HashMap<String,Table> tables;
//   HashMap<String,Register> registers;
//   packet_in pin; 
//   packet_out pout;
// }

// struct standard_metadata_t {
//   struct BitVec *ingress_port;
//   struct BitVec *egress_spec;
//   struct BitVec *egress_port;
//   struct BitVec *instance_type;
//   struct BitVec *packet_length;
//   struct BitVec *enq_timestamp;
//   struct BitVec *enq_qdepth;
//   struct BitVec *deq_timedelta;
//   struct BitVec *deq_qdepth;
//   struct BitVec *ingress_global_timestamp;
//   struct BitVec *egress_global_timestamp;
//   struct BitVec *mcast_grp;
//   struct BitVec *egress_rid;
//   struct BitVec *checksum_error;
//   unsigned int parser_error;
//   struct BitVec *priority;
// };

void init_standard_metada (struct standard_metadata_t* meta){
    init_bitvec(meta->ingress_port, 0,9,"0");
    init_bitvec(meta->egress_spec,0,9,"0");
    init_bitvec(meta->egress_port,0,9,"0");
    init_bitvec(meta->instance_type,0,32,"0");
    init_bitvec(meta->packet_length,0,32,"0");
    init_bitvec(meta->enq_timestamp,0,32,"0");
    init_bitvec(meta->enq_qdepth,0,19,"0");
    init_bitvec(meta->deq_timedelta,0,32,"0");
    init_bitvec(meta->deq_qdepth,0,19,"0");
    init_bitvec(meta->ingress_global_timestamp,0,48,"0");
    init_bitvec(meta->egress_global_timestamp,0,48,"0");
    init_bitvec(meta->mcast_grp,0,16,"0");
    init_bitvec(meta->egress_rid,0,16,"0");
    init_bitvec(meta->checksum_error,0,1,"0");
    meta->parser_error = 0;
    init_bitvec(meta->priority,0,3,"0");
}


int main( int argc, char *argv[] ) //first argument is the location of the input packet, second argument is ingress_port
{
  if(argc != 3){
    printf("wrong number of arguments");
    return 2;
  }
  FILE *fp;
  fp = fopen(argv[1], "r");
  unsigned char buff [256]; //a temporary limit
  packet_out pout;
  packet_in pin;
  fscanf(fp, "%s", buff);
  pin.in = buff;
  struct H h;
  struct M m;
  struct standard_metadata_t meta;
  init_standard_metada(&meta);
  init_bitvec(meta.ingress_port, 0,9,argv[2]);
  int result;
  result = parser (&pin, &h , &m, &meta);
  if(!result){
    printf("parser rejected the packet");
  }else{
  result = verify (&h, &m);
  if(!result){
    printf("verify failed");
  }else{
  result = ingress (&h, &m, &meta);
  if(!result){
    printf("ingress failed");
  }else{
  result = egress (&h, &m, &meta);
  if(!result){
    printf("egress failed");
  }else{
  result = compute(&h, &m);
  if(!result){
    printf("compute checksum failed");
  }else{
  result = deparser(&pout, h);
  if(!result){
    printf("deparser failed");
  }else{
    printf("packet successfully emitted");
  }
  }
  }
  }
  }
  }
}