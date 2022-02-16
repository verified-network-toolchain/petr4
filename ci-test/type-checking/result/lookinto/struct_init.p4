/petr4/ci-test/type-checking/testdata/p4_16_samples/struct_init.p4
\n
struct PortId_t { bit<9> _v; }

const PortId_t PSA_CPU_PORT = {9w192};

struct metadata_t {
    PortId_t foo;
}

control I(inout metadata_t meta) {
    apply {
        if (meta.foo == PSA_CPU_PORT) {
            meta.foo._v = meta.foo._v + 1;
        }
    }
}

control C<M>(inout M m);
package top<M>(C<M> c);

top(I()) main;************************\n******** petr4 type checking result: ********\n************************\n
