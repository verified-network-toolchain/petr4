const bit<8> t = 8w8;

bit<8> addt(in bit<8> x) {
  return t + x;
}

const bit<8> t = 8w4;
const bit<8> x = addt(8w34); //should use lexical scope and get 42

package EmptyPackage();
EmptyPackage() main;
