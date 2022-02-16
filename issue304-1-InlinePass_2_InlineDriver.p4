extern X {
    X();
    bit<32> b();
    abstract void a(inout bit<32> arg);
}

control c(inout bit<32> y) {
    @name("x") X() x_0 = {
        void a(inout bit<32> arg) {
            bit<32> tmp;
            bit<32> tmp_0;
            bit<32> tmp_1;
            tmp = arg;
            tmp_0 = this.b();
            tmp_1 = tmp + tmp_0;
            arg = tmp_1;
        }
    };
    apply {
        x_0.a(y);
    }
}

control t(inout bit<32> b) {
    @name("c1") c() c1_0;
    @name("c1.x") X() c1_x = {
        void a(inout bit<32> arg) {
            @name("c1.tmp") bit<32> c1_tmp;
            @name("c1.tmp_0") bit<32> c1_tmp_0;
            @name("c1.tmp_1") bit<32> c1_tmp_1;
            c1_tmp = arg;
            c1_tmp_0 = this.b();
            c1_tmp_1 = c1_tmp + c1_tmp_0;
            arg = c1_tmp_1;
        }
    };
    @name("c2") c() c2_0;
    @name("c2.x") X() c2_x = {
        void a(inout bit<32> arg) {
            @name("c2.tmp") bit<32> c2_tmp;
            @name("c2.tmp_0") bit<32> c2_tmp_0;
            @name("c2.tmp_1") bit<32> c2_tmp_1;
            c2_tmp = arg;
            c2_tmp_0 = this.b();
            c2_tmp_1 = c2_tmp + c2_tmp_0;
            arg = c2_tmp_1;
        }
    };
    apply {
        {
            c1_x.a(b);
        }
        {
            c2_x.a(b);
        }
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;

