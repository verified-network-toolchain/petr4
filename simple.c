#include "petr4-runtime.h"
/*todo: Action*/
typedef struct simple_h {
  bool __header_valid;
  bit8 src;
  bit8 dst;
} simple_h;
typedef struct header_t {
  simple_h simple;
} header_t;
typedef struct MyP_state {
  packet_in pkt;
  header_t hdrs;
}
MyP_state;
void MyP(MyP_state* state)
  {
  int __next_state = 0;
  while ((__next_state >= 0))
    {
    switch (__next_state) {
      case 0:
      extract(state->pkt, &((state->hdrs).simple), 16);
      __next_state = -1;
      break;
    }
  };
}
typedef struct MyC_state {
  header_t hdrs;
  bool forward;
}
MyC_state;
void do_forward(MyC_state *state) {
  state->forward = true;
}
void do_drop(MyC_state *state) {
  state->forward = false;
}
void t(MyC_state *state)
  {
  if (state->hdrs.simple.dst!=0) {
    do_forward(state);
  }else {
     do_drop(state);
  };
}
void MyC(MyC_state* state) {
  t(state);
}
typedef struct MyD_state {
  packet_out pkt;
  header_t hdrs;
}
MyD_state;
void MyD(MyD_state* state) {
  (state);
}
/*todo: Instantiation*/
