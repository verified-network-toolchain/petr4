control c(inout bit<8> val)(int a) {
    apply {
        val = (bit<8>)a;
    }
}

control c_0(inout bit<8> val) {
    apply {
        val = (bit<8>)0;
    }
}

control ingress(inout bit<8> a) {
    @name("x") c_0() x_0;
    apply {
        x_0.apply(a);
    }
}

control i(inout bit<8> a);
package top(i _i);
top(ingress()) main;

