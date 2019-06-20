const bit<8> t = 8w8;

bit<8> addt(in bit<8> x) {
  return t + x;
}

const bit<8> t = 8w4; //type check should reject variable name shadowing
const bit<8> x = addt(8w34); //38, but not a well-formed program

package EmptyPackage();
EmptyPackage() main;
