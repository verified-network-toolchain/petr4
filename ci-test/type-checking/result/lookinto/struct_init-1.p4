/petr4/ci-test/type-checking/testdata/p4_16_samples/struct_init-1.p4
\n
struct PortId_t { bit<9> _v; }
header H { bit<32> b; }

const PortId_t PSA_CPU_PORT = { _v = 9w192 };

struct metadata_t {
    PortId_t foo;
}

control I(inout metadata_t meta) {
    apply {
        PortId_t p = { _v = 0 };
        H h = { b = 1 };
        if (meta.foo == PSA_CPU_PORT) {
            meta.foo._v = meta.foo._v + 1;
            h = { b = 2 };
            if (h == (H) { b = 1 })
                h = { b = 2 };
        }
    }
}

control C<M>(inout M m);
package top<M>(C<M> c);

top(I()) main;************************\n******** petr4 type checking result: ********\n************************\n
struct PortId_t {
  bit<9> _v;
}
header H {
  bit<32> b;
}
const PortId_t PSA_CPU_PORT = {_v = 9w192};
struct metadata_t {
  PortId_t foo;
}
control I(inout metadata_t meta) {
  apply
    {
    PortId_t p = {_v = 0};
    H h = {b = 1};
    if (meta.foo==PSA_CPU_PORT)
      {
      meta.foo._v = meta.foo._v+1;
      h = {b = 2};
      if (h==(H) {b = 1}) 
        h = {b = 2};
    }
  }
}
control C<M> (inout M m);
package top<M0> (C<M0> c);
top(I()) main;

