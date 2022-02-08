control c() {
    bit<16> f = (bit<16>)16w0;
    bit<128> y = (bit<128>)128w0;
    action a() {
        y = (bit<128>)f;
    }
    apply {
        exit;
        a();
    }
}

control e();
package top(e e);
top(c()) main;

