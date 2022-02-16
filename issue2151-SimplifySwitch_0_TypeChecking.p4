control c() {
    @name("f") bit<16> f_0;
    @name("y") bit<128> y_0;
    @name("a") action a_0() {
        y_0 = (bit<128>)f_0;
    }
    apply {
        f_0 = 16w0;
        y_0 = 128w0;
        exit;
        a_0();
    }
}

control e();
package top(e e);
top(c()) main;

