const bool a = - (8s8) == -8;
const bool b = 4 != -(8s3);
const bool c = -7 < 19s12;
const bool d = 18s12 > -7;
const bool e = -(6s8) <= -(6s7);
const bool f = 9s7 <= 9s7;
const bool g = 6s8 >= 6s7;
const bool h = 9s7 >= 9s7; // all true
const int<8> i = -(8s214); //42
const int<8> j = +(8s42); //42
const int<8> k = (-8s7 + -8s3) + 52; //42
const int<8> l = (-8s42) - (-8s84); //42
const int<8> m = -8s2 * 3 * -8s7; //42
const int<8> n = 8s46 & 8s59; //42
const int<8> o = 8s34 | 8s8; //42
const int<8> p = ~ (-8s43); //42
const int<8> q = 8s25 ^ 8s51; //42
const int<8> r = 8s7 |+| 8s3 |+| 32; //42
const int<8> s = 8s117 |-| 8s75; //42
const int<8> t = 8s7 + 8s3 + 8s32 + 128 + 8s128; //42, should wrap around
const int<8> u = 8s117 - 8s75 - 8s128 - 8s128; //42, should wrap around
const int<8> v = 8s7 |+| 8s3 |+| 8s32 |+| 8s128 |+| 8s128; //127, should saturate
const int<8> w = 8s117 |-| 8s75 |-| 8s128 |-| 8s128; //-128, should saturate
const int<8> x = (-8s127 - 1) & -8s1; //-128

package EmptyPackage();
EmptyPackage() main;

/* lots of bugs */
