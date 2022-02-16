extern bit<1> f(inout bit<1> x, in bit<1> y);
extern bit<1> g(inout bit<1> x);
header H {
    bit<1> z;
}

control c<T>(inout T t);
package top<T>(c<T> _c);
control my(inout H[2] s) {
    bit<1> hsVar;
    @name("my.a") bit<1> a_0;
    @name("my.tmp") bit<1> tmp;
    @name("my.tmp_0") bit<1> tmp_0;
    @name("my.tmp_1") bit<1> tmp_1;
    @name("my.tmp_3") bit<1> tmp_3;
    @name("my.tmp_4") bit<1> tmp_4;
    @name("my.tmp_5") bit<1> tmp_5;
    @name("my.tmp_6") bit<1> tmp_6;
    @name("my.tmp_8") bit<1> tmp_8;
    @name("my.tmp_10") bit<1> tmp_10;
    @hidden action act() {
        tmp_3 = s[1w0].z;
    }
    @hidden action act_0() {
        tmp_3 = s[1w1].z;
    }
    @hidden action side_effects30() {
        tmp_3 = hsVar;
    }
    @hidden action side_effects27() {
        a_0 = 1w0;
        tmp = 1w0;
        tmp_0 = g(a_0);
        tmp_1 = f(tmp, tmp_0);
        a_0 = tmp_1;
    }
    @hidden action act_1() {
        s[1w0].z = tmp_3;
    }
    @hidden action act_2() {
        s[1w1].z = tmp_3;
    }
    @hidden action act_3() {
        tmp_4 = g(a_0);
        tmp_5 = f(tmp_3, tmp_4);
    }
    @hidden action act_4() {
        tmp_8 = s[1w0].z;
    }
    @hidden action act_5() {
        tmp_8 = s[1w1].z;
    }
    @hidden action side_effects31() {
        tmp_8 = hsVar;
    }
    @hidden action side_effects30_0() {
        a_0 = tmp_5;
        tmp_6 = g(a_0);
    }
    @hidden action act_6() {
        s[1w0].z = tmp_8;
    }
    @hidden action act_7() {
        s[1w1].z = tmp_8;
    }
    @hidden action act_8() {
        tmp_10 = f(tmp_8, a_0);
    }
    @hidden action side_effects34() {
        s[1w0].z = g(a_0);
    }
    @hidden action side_effects34_0() {
        s[1w1].z = g(a_0);
    }
    @hidden action side_effects31_0() {
        a_0 = tmp_10;
        a_0 = g(a_0);
        a_0 = g(a_0);
    }
    apply {
        side_effects27();
        if (tmp_1 == 1w0) {
            act();
        } else if (tmp_1 == 1w1) {
            act_0();
        } else if (tmp_1 >= 1w1) {
            side_effects30();
        }
        act_3();
        if (tmp_1 == 1w0) {
            act_1();
        } else if (tmp_1 == 1w1) {
            act_2();
        }
        side_effects30_0();
        if (tmp_6 == 1w0) {
            act_4();
        } else if (tmp_6 == 1w1) {
            act_5();
        } else if (tmp_6 >= 1w1) {
            side_effects31();
        }
        act_8();
        if (tmp_6 == 1w0) {
            act_6();
        } else if (tmp_6 == 1w1) {
            act_7();
        }
        side_effects31_0();
        if (a_0 == 1w0) {
            side_effects34();
        } else if (a_0 == 1w1) {
            side_effects34_0();
        }
    }
}

top<H[2]>(my()) main;

