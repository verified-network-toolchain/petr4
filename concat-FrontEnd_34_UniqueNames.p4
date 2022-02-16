control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    apply {
        @name("a") bit<8> a_0 = 8w0xf;
        @name("b") bit<16> b_0 = 16w0xf;
        x = a_0 ++ b_0 ++ a_0 + (b_0 ++ (a_0 ++ a_0));
    }
}

top(c()) main;

