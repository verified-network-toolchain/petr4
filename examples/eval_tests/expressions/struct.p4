struct my_struct {
  bit<8> n;
  bool b;
}

my_struct f(in bit<8> a, in bool b) {
    my_struct ans;
    ans.n = a;
    ans.b = b;
    return ans;
}

const my_struct s = { 42, true };
const bit<8> num = s.n; //42
const bool boo = s.b; //true

const my_struct s2 = f(42,true);
const bit<8> num2 = s2.n; //42
const bit<8> boo2 = s2.b; //true

package EmptyPackage();
EmptyPackage() main;
