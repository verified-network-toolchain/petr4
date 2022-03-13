#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gmp.h"
#include <assert.h>
#include <math.h> 
#include "Petr4Runtime.h"

typedef struct Register {
    int size;
    void** vals;
} Register;



typedef struct State {
  HashMap<String,Table> tables;
  HashMap<String,Register> registers;
  packet_in pin; 
  packet_out pout;
}

typedef struct standard_metadata_t {
    BitVec      ingress_port;
    BitVec      egress_spec;
    BitVec     egress_port;
    BitVec     instance_type;
    BitVec     packet_length;

    BitVec enq_timestamp;
    BitVec enq_qdepth;
    BitVec deq_timedelta;
    BitVec deq_qdepth;

    BitVec ingress_global_timestamp;
    BitVec egress_global_timestamp;
    BitVec mcast_grp;
    BitVec egress_rid;
    BitVec  checksum_error;
    error parser_error;
    BitVec priority;
}


int main(void)
{
  struct packet_out _p_e_t_r_4_0b111011;
  struct packet_in _p_e_t_r_4_0b111010;
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b111001;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b111000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b110111;
  my_parser
    (_p_e_t_r_4_0b111010, &_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000,
     &_p_e_t_r_4_0b111001);
  my_verify(&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000);
  my_ingress
    (&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000, &_p_e_t_r_4_0b111001);
  my_egress
    (&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000, &_p_e_t_r_4_0b111001);
  my_compute(&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000);
  my_deparser(_p_e_t_r_4_0b111011, _p_e_t_r_4_0b110111);
}