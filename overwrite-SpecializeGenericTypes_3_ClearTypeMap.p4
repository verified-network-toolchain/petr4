control c(out bit<32> x);
package top(c _c);
control my(out bit<32> x) {
    apply {
        x = (bit<32>)32w1;
        x = (bit<32>)32w2;
    }
}

top(my()) main;

