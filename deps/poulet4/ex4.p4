control CBit(inout bit<8> x) {
  apply { }
}
control CInt(inout int<8> x) {
  apply { }
}

control C<T>(inout T param);

package P<T>(C<T> ingress=CBit(), C<T> egress=CInt());
