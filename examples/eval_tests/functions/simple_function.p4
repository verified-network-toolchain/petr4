bit<8> add(in bit<8> a, in bit<8> b) {
  return a + b;
}

const bit<8> x = add(8w21, 8w21);
const bit<8> y = add(8w13, 8w29);

package EmptyPackage();
EmptyPackage() main;
