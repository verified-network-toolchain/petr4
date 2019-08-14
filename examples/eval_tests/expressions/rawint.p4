const bool a = 8 == 8;
const bool b = 4 != 7;
const bool c = 7 < 12;
const bool d = 12 > 7;
const bool e = 7 <= 8;
const bool f = 7 <= 7;
const bool g = 8 >= 7;
const bool h = 7 >= 7; // all true
const bit<8> i = -(214); //42
const bit<8> j = +(42); //42
const bit<8> k = (7 + 3) + 32; //42
const bit<8> l = 117 - 75; //42
const bit<8> m = 2 * 3 * 7; //42
const bit<8> n = 126 / 3; //42
const bit<8> o  = 292 % 50; //42

package EmptyPackage();
EmptyPackage() main;

/* lots of bugs */
