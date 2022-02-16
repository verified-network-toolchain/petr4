header header_h {
    bit<8> field;
}

struct struct_t {
    header_h[4] stack;
}

control ctrl(inout struct_t input, out header_h output) {
    @name("tmp0") header_h tmp0_0;
    @name("tmp1") header_h tmp1_0;
    @name("act") action act_0() {
        tmp0_0 = input.stack[0];
        input.stack.pop_front(1);
        tmp1_0 = tmp0_0;
    }
    apply {
        tmp0_0.setInvalid();
        tmp1_0.setInvalid();
        act_0();
        output = tmp1_0;
    }
}

control MyControl<S, H>(inout S data, out H output);
package MyPackage<S, H>(MyControl<S, H> ctrl);
MyPackage<struct_t, header_h>(ctrl()) main;

