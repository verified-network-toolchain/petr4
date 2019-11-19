const bool a = 8w8 == 8;
const bool b = 4 != 7w3;
const bool c = 7 < 19w12;
const bool d = 18w12 > 7;
const bool e = 6w7 <= 6w8;
const bool f = 9w7 <= 9w7;
const bool g = 6w8 >= 6w7;
const bool h = 9w7 >= 9w7; // all true
const bit<8> i = -(214); //42
const bit<8> j = +(8w42); //42
const bit<8> k = (8w7 + 8w3) + 32; //42
const bit<8> l = 8w117 - 8w75; //42
const bit<8> m = 8w2 * 3 * 8w7; //42
const bit<8> n = 8w46 & 59; //42
const bit<8> o = 34 | 8w8; //42
const bit<8> p = ~ 8w42; //213
const bit<8> q = 8w25 ^ 51; //42
const bit<8> r = 8w7 |+| 8w3 |+| 32; //42
const bit<8> s = 8w117 |-| 8w75; //42
const bit<8> t = 8w7 + 8w3 + 8w32 + 128 + 8w128; //42, should wrap around
const bit<8> u = 8w117 - 8w75 - 8w128 - 8w128; //42, should wrap around
const bit<8> v = 8w7 |+| 8w3 |+| 8w32 |+| 8w128 |+| 8w128; //255, should saturate
const bit<8> w = 8w117 |-| 8w75 |-| 8w128 |-| 8w128; //0, should saturate
const bit<8> x = 2 ++ 4w10; //42
const bit<6> y = 12w3927[4w8:2w3]; //42
const bit z = 4w7[1w1:1w1]; //1

package EmptyPackage();
EmptyPackage() main;

/* lots of bugs */
