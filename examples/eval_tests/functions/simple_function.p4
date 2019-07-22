bit<8> add(in bit<8> a, in bit<8> b) {
  return a + b;
}

const bit<8> x = add(21, 21); //42
const bit<8> y = add(13, 29); //42

package EmptyPackage();
EmptyPackage() main;
