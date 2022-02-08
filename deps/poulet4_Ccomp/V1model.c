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