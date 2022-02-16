/petr4/ci-test/type-checking/testdata/p4_16_samples/twoPipe.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

extern packet_in {}
extern packet_out {}
struct inControl {}

struct outControl {}

parser Parser<IH>(packet_in b, out IH parsedHeaders);

control IMAP<T, IH, OH>(in IH inputHeaders, 
                        in inControl inCtrl,
                        out OH outputHeaders,
                        out T toEgress,
                        out outControl outCtrl);

control OMAP<T, IH, OH>(in IH inputHeaders, 
                        in inControl inCtrl,
                        in T fromIngress,
                        out OH outputHeaders,
                        out outControl outCtrl); 

control Deparser<OH>(in OH outputHeaders, packet_out b);

package Ingress<T, IH, OH>(Parser<IH> p,
                           IMAP<T, IH, OH> map,
                           Deparser<OH> d);

package Egress<T, IH, OH>(Parser<IH> p,
                          OMAP<T, IH, OH> map,
                          Deparser<OH> d);

package Switch<T>(
    // no connection between Ingress.IH and Egress.IH
    Ingress<T, _, _> ingress,
    Egress<T, _, _> egress
);
************************\n******** petr4 type checking result: ********\n************************\n
extern packet_in  {
  }
extern packet_out  {
  }
struct inControl {
  
}
struct outControl {
  
}
parser Parser<IH> (packet_in b, out IH parsedHeaders);
control IMAP<T, IH0, OH>
  (in IH0 inputHeaders,
   in inControl inCtrl,
   out OH outputHeaders,
   out T toEgress,
   out outControl outCtrl);
control OMAP<T1, IH2, OH3>
  (in IH2 inputHeaders,
   in inControl inCtrl,
   in T1 fromIngress,
   out OH3 outputHeaders,
   out outControl outCtrl);
control Deparser<OH4> (in OH4 outputHeaders, packet_out b);
package Ingress<T5, IH6, OH7>
  (Parser<IH6> p, IMAP<T5, IH6, OH7> map, Deparser<OH7> d);
package Egress<T8, IH9, OH10>
  (Parser<IH9> p, OMAP<T8, IH9, OH10> map, Deparser<OH10> d);
package Switch<T11> (Ingress<T11, _, _> ingress, Egress<T11, _, _> egress);

