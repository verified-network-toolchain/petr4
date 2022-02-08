control c(inout bit<16> y) {
    @name("x") bit<32> x;
    @name("arg") bit<32> arg;
    @name("a") action a_0() {
        arg = x;
        y = (bit<16>)arg;
    }
    apply {
        x = 32w2;
        a_0();
    }
}

control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;

