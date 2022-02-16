control ctrl() {
    apply {
        bit<32> a;
        bit<32> b;
        bit<32> c;
        a = (bit<32>)32w0;
        b = (bit<32>)32w1;
        c = (bit<32>)32w2;
        if (a == 32w0) {
            b = (bit<32>)32w2;
            exit;
            c = (bit<32>)32w3;
        } else {
            b = (bit<32>)32w3;
            exit;
            c = (bit<32>)32w4;
        }
        c = (bit<32>)32w5;
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

