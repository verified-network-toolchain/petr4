struct my_struct {
  bit<8> n;
  bool b;
}

const my_struct s = { 42, true };

package EmptyPackage();
EmptyPackage() main;
