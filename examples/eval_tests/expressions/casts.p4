const bool a = (bool) 1w1; //true
const bit<4> b = (bit<4>) 8w0b00011111; //15
const bit<4> c = (bit<4>) 4s0b1111; //15
const bit<4> d = 20; //4
const int<4> e = (int<4>) 8w0b10001111; //-1
const int<4> f = (int<4>) 4w0b1111; //-1
const int<4> g = 24; //-8

typedef bit<32> u32;
const u32 h = 5;
const bit<32> i = (bit<32>) h;

package EmptyPackage();
EmptyPackage() main;
