control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    apply {
        x = 32w8;
        x = 32w8;
        x = 32w8;
        x = 32w8;
        x = 32w2;
        x = 32w2;
        x = 32w2;
        x = 32w2;
        x = 32w15;
        x = 32w15;
        x = 32w1;
        x = 32w1;
        x = 32w2;
        x = 32w1;
        x = 32w1;
        x = 32w1;
        x = 32w7;
        x = 32w7;
        x = 32w6;
        x = 32w6;
        x = 32w40;
        x = 32w40;
        x = 32w2;
        x = 32w2;
        x = 32w5;
        x = 32w5;
        x = 32w17;
        @name("w") bool w_0;
        w_0 = false;
        w_0 = false;
        w_0 = true;
        w_0 = true;
        w_0 = false;
        w_0 = false;
        w_0 = true;
        w_0 = true;
        w_0 = false;
        w_0 = false;
        w_0 = true;
        w_0 = true;
        w_0 = false;
        w_0 = true;
        w_0 = true;
        w_0 = false;
        @name("z") bit<8> z_0;
        z_0 = 8w0;
        z_0 = 8w0;
        z_0 = 8w128;
        z_0 = 8w128;
        z_0 = 8w0;
        z_0 = 8w0;
        z_0 = 8w0;
    }
}

top(c()) main;

