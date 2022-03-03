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

void read(out T result, in bit<32> index);


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