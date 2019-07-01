header my_header {
  bit<2> first;
  bit<2> second;
}

my_header f(in bit<2> a, in bit<2> b) {
    my_header ans;
    ans.setValid();
    ans.first = a;
    ans.second = b;
    return ans;
}

my_header g(in my_header hdr) {
    hdr.setInvalid();
    return hdr;
}

const my_header head = { 1, 0 };
const bool a = head.isValid(); //true; initializing with a list expression makes it valid
const bit<2> b = head.first; // 1
const bit<2> c = head.second; // 0

const my_header head2 = g(head);
const bool d = head2.isValid(); //false
const bit<2> e = head2.first; //1
const bit<2> h = head2.second;//0

const my_header head3 = f(2w2,2w3);
const bool i = head3.isValid(); //true
const bit<2> j = head3.first; //2
const bit<2> k = head3.second; //3

package EmptyPackage();
EmptyPackage() main;
