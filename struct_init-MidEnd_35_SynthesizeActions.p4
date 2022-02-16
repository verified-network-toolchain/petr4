struct PortId_t {
    bit<9> _v;
}

struct metadata_t {
    bit<9> _foo__v0;
}

control I(inout metadata_t meta) {
    @hidden action struct_init12() {
        meta._foo__v0 = meta._foo__v0 + 9w1;
    }
    apply {
        if (meta._foo__v0 == 9w192) {
            struct_init12();
        }
    }
}

control C<M>(inout M m);
package top<M>(C<M> c);
top<metadata_t>(I()) main;

