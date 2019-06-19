void swap(out bit a, out bit b) {
  bit tmp = a;
  a = b;
  b = tmp;
  return;
}

bit<2> swapped(in bit<2> x) {
  bit<2> tmp = x;
  swap(tmp[1:1], tmp[0:0]);
  return tmp;
}

const bit<2> a = swapped(2w0);
const bit<2> b = swapped(2w1);
const bit<2> c = swapped(2w2);
const bit<2> d = swapped(2w3);

package EmptyPackage();
EmptyPackage() main;
/* doubles as a tricky variable naming test */

/* currently broken; unimplmented; probably the method call in line 10 */
