bit<8> flush_bits(in bit<8> n, in bit<3> m, in bit<3> l) {
    n[m:l] = 0;
    return n;
}

bit<8> sat_bits(in bit<8> n, in bit<3> m, in bit<3> l) {
    n[m:l] = 7;
    return n;
}

const bit<8> a = 43;
const bit<5> b = a[6:2]; //10
const bit<8> c = 42 + 64;
const bit<5> d = c[6:2]; //26
const bit e = a[0:0]; //1
const bit f = a[2:2]; //0
const bit g = a[1:1]; //1
const bit<2> h = a[1:0]; //3
const bit<2> i = a[5:4]; //2
const bit<8> j = flush_bits(a, 6, 1); //1
const bit<8> k = flush_bits(a, 0, 0); //42
const bit<8> l = sat_bits(a, 4 ,2); //63

package EmptyPackage();
EmptyPackage() main;
