void swap(inout bit a, inout bit b) {
  bit tmp = a;
  a = b;
  b = tmp;
  return;
}

bit<2> swapped(in bit<2> x) {
  swap(x[1:1], x[0:0]);
  return x;
}

const bit<2> a = swapped(0); //0
const bit<2> b = swapped(1); //2
const bit<2> c = swapped(2); //1
const bit<2> d = swapped(3); //3

package EmptyPackage();
EmptyPackage() main;
