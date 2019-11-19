const bool a = true;
const bool b = false;
const bool c = true && true;
const bool d = true && false;
const bool e = false && true;
const bool f = false && false;
const bool g = true || true;
const bool h = true || false;
const bool i = false || true;
const bool j = false || false;
const bool k = !true;
const bool l = !false;
const bool m = true == true;
const bool n = false == false;
const bool o = false == true;
const bool p = true == false;
const bool q = true != true;
const bool r = true != false;
const bool s = false != true;
const bool t = false != false;
const bit<1> u = true ? 1 : 0;
const bit<1> v = false ? 1 : 0;

package EmptyPackage();
EmptyPackage() main;

/* expected mappings:
true
false
true
false
false
false
true
true
true
false
false
true
true
true
false
false
false
true
true
false
1
0
*/
