extern bit<1> f(inout bit<1> x, in bit<1> y);
extern bit<1> g(inout bit<1> x);
header H {
    bit<1> z;
}

control c<T>(inout T t);
package top<T>(c<T> _c);
control my(inout H[2] s) {
    @name("a") bit<1> a;
    @name("tmp") bit<1> tmp_11;
    @name("tmp_0") bit<1> tmp_12;
    @name("tmp_1") bit<1> tmp_13;
    @name("tmp_2") bit<1> tmp_14;
    @name("tmp_3") bit<1> tmp_15;
    @name("tmp_4") bit<1> tmp_16;
    @name("tmp_5") bit<1> tmp_17;
    @name("tmp_6") bit<1> tmp_18;
    @name("tmp_7") bit<1> tmp_19;
    @name("tmp_8") bit<1> tmp_20;
    @name("tmp_9") bit<1> tmp_21;
    @name("tmp_10") bit<1> tmp_22;
    apply {
        a = 1w0;
        tmp_11 = a;
        tmp_12 = g(a);
        tmp_13 = f(tmp_11, tmp_12);
        a = tmp_13;
        tmp_14 = a;
        tmp_15 = s[tmp_14].z;
        tmp_16 = g(a);
        tmp_17 = f(tmp_15, tmp_16);
        s[tmp_14].z = tmp_15;
        a = tmp_17;
        tmp_18 = g(a);
        tmp_19 = tmp_18;
        tmp_20 = s[tmp_19].z;
        tmp_21 = a;
        tmp_22 = f(tmp_20, tmp_21);
        s[tmp_19].z = tmp_20;
        a = tmp_22;
        a = g(a);
        a = g(a);
        s[a].z = g(a);
    }
}

top<H[2]>(my()) main;

