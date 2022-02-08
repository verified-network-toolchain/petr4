control c_0(inout bit<8> val) {
    apply {
        val = 8w0;
    }
}

control ingress(inout bit<8> a) {
    @name("x") c_0() x_0;
    apply {
        {
            a = 8w0;
        }
    }
}

control i(inout bit<8> a);
package top(i _i);
top(ingress()) main;

