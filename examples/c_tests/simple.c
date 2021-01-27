#include "petr4-runtime.h"

typedef struct simple_h {
  bool valid;
  bit8 src;
  bit8 dst;
} simple_h;
typedef struct headers {
  simple_h simple;
} headers;
typedef struct P_state {
  packet_in pkt;
  headers hdrs;
} P_state;
void P(P_state* state) {
  extract(state->pkt, &state->hdrs.simple, 16);
}
typedef struct C_state {
  headers hdrs;
  bool forward;
} C_state;
void C_do_forward(C_state* state, headers* h) {
  state->forward = true;
}
void C_do_drop(C_state* state) {
  state->forward = false;
}
void C(C_state* state) {
  if(state->hdrs.simple.dst != 0) {
    C_do_forward(state);
  } else { 
    C_do_drop(state);
  }
}
typedef struct D_state {
  packet_out pkt;
  headers hdrs;
} D_state;
void D(D_state* state) {
    emit(state->pkt, &state->hdrs.simple, 16);
}
int main() {
  P_state p;
  C_state c;
  D_state d;
  p.pkt = "Hi";
  P(&p);
  c.hdrs = p.hdrs;
  C(&c);
  d.hdrs = c.hdrs;
  d.pkt = malloc(2);
  D(&d);
  printf("Out: %s\nForward: %d\n", d.pkt, c.forward);
  return 0;
}
