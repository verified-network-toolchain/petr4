struct my_struct {
  bit<8> n;
  bool b;
}

const my_struct s = { 42, true };
const bit<8> num = s.n;
const bool boo = s.b;

package EmptyPackage();
EmptyPackage() main;
