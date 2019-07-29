const bit<8> a = (8w0b00101010 << 6) >> 7; //1
const bit<8> b = (8w0b00101010 << 2); //168
const bit<8> c = 8w168 >> 2; //42
const int<8> d = (8s42 << 6) >> 7; //-1
const int<8> e = 8s42 << 2; //-88
const int<8> f = (8s42 << 2) >> 2; //-22

package EmptyPackage();
EmptyPackage() main;
