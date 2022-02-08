control ctrl(out bit<32> c) {
    bit<32> x;
    action e() {
        exit;
        x = (bit<32>)32w1;
    }
    apply {
        bit<32> a;
        bit<32> b;
        a = (bit<32>)32w0;
        b = (bit<32>)32w1;
        c = (bit<32>)32w2;
        if (a == 32w0) {
            b = (bit<32>)32w2;
            e();
            c = (bit<32>)32w3;
        } else {
            b = (bit<32>)32w3;
            e();
            c = (bit<32>)32w4;
        }
        c = (bit<32>)32w5;
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

