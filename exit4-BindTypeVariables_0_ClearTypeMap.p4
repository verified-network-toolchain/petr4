control ctrl() {
    action e() {
        exit;
    }
    table t {
        actions = {
            e();
        }
        default_action = e();
    }
    apply {
        bit<32> a;
        bit<32> b;
        bit<32> c;
        a = (bit<32>)32w0;
        b = (bit<32>)32w1;
        c = (bit<32>)32w2;
        if (t.apply().hit) {
            b = (bit<32>)32w2;
            t.apply();
            c = (bit<32>)32w3;
        } else {
            b = (bit<32>)32w3;
            t.apply();
            c = (bit<32>)32w4;
        }
        c = (bit<32>)32w5;
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

