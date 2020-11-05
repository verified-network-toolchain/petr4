// concrete default parameter in package
struct emp_t { }
control nothing(inout emp_t hdr) { apply { } }

control C<H>(inout H hdr);
package P<H>(C<H> c = nothing());

P<_>() main;


// concrete default parameter in function
T f<T>(in T x = 8w10) {
  return x;
}

control MyC() {
  apply {
    bit<8> x = f();
  }
}
